import os
import shutil
from os.path import dirname
from os.path import isdir
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values
from app.core.task.dir_info import generate_dir_info
from app.core.task.results import collect_benchmark_result
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


def construct_container_volumes(
    dir_info: DirectoryInfo, extra_volumes: Optional[Dict[str, Any]] = None
) -> Dict[str, Dict[str, str]]:
    volume_list: Dict[str, Dict[str, str]] = {
        dir_info["local"]["logs"]: {"bind": "/logs", "mode": "rw"},
        dir_info["local"]["setup"]: {
            "bind": dir_info["container"]["setup"],
            "mode": "rw",
        },
        dir_info["local"]["aux"]: {"bind": dir_info["container"]["aux"], "mode": "rw"},
        dir_info["local"]["base"]: {
            "bind": dir_info["container"]["base"],
            "mode": "rw",
        },
        "/var/run/docker.sock": {"bind": "/var/run/docker.sock", "mode": "rw"},
    }

    if extra_volumes:
        volume_list.update(extra_volumes)
    return volume_list


def _tool_based_image(
    bug_image_id: str,
    tool: AbstractTool,
    dir_info: DirectoryInfo,
    bug_info: Dict[str, Any],
    tag: Optional[str],
) -> str:

    dockerfile_name = "Dockerfile-{}-{}".format(tool.name, bug_image_id)
    if tag and tag != "":
        dockerfile_name += "-{}".format(tag)

    tmp_dockerfile = join(
        dir_info["local"]["setup"],
        dockerfile_name,
    )
    os.makedirs(dirname(tmp_dockerfile), exist_ok=True)
    with open(tmp_dockerfile, "w") as dock_file:
        dock_file.write("FROM {}\n".format(tool.image_name))
        dock_file.write("ADD . {0}\n".format(dir_info["container"]["setup"]))

        res, (output, error) = utilities.run_command(
            f"getent group {definitions.GROUP_NAME} | cut -d: -f3"
        )
        if not output or output.decode() == "":
            utilities.error_exit(
                f"Cannot the id of the group {definitions.GROUP_NAME}. Ensure that it exists"
            )

        group_id = output.decode().strip()

        emitter.debug(f"Group {definitions.GROUP_NAME} has id {group_id} ")

        home_directory = "/root/"
        prefix = ""
        if not tool.runs_as_root:
            prefix = "sudo"
            home_directory = f"/home/{tool.image_user}/"
            if tool.sudo_password:
                prefix = f'echo "{tool.sudo_password}\\n" | sudo -S'

        # Create a special group to ensure that files are accessible
        dock_file.write(
            f"RUN {prefix} bash -c 'groupadd -g {group_id} {definitions.GROUP_NAME}' \n"
        )

        # Make all user's primary group to be our special group
        dock_file.write(
            f'RUN {prefix} bash -c "cut -d: -f1 /etc/passwd | xargs -i usermod -g {definitions.GROUP_NAME} {{}} "\n'
        )

        ownership = ""
        if tool.image_user != "root":
            ownership = f"--chown={tool.image_user}:{definitions.GROUP_NAME}"

        dock_file.write(
            "COPY --from={0} {2} {1} {1}\n".format(
                bug_image_id, values.container_base_experiment, ownership
            )
        )
        dock_file.write(
            "COPY --from={0} {2} {1} {1}\n".format(bug_image_id, "/logs", ownership)
        )
        dock_file.write(
            "COPY --from={0} {3} {1} {2}\n".format(
                bug_image_id, "/root/", home_directory, ownership
            )
        )

        src_dir = bug_info.get(
            definitions.KEY_SOURCE_DIRECTORY,
            join(dir_info["container"]["experiment"], "src"),
        )
        if str(src_dir)[-1] == "/":
            src_dir = src_dir[:-1]
        pom_dir = os.path.dirname(os.path.dirname(os.path.dirname(src_dir))) or "."
        pom_file = f"{dir_info['container']['experiment']}/src/{pom_dir}/pom.xml"
        if tool.name.lower() in ["et", "grt5"]:
            dock_file.write(
                "RUN mvnd -1 -B -Dmvnd.daemonStorage=/root/workflow/default "
                "-ff -Djava.awt.headless=true -Dmaven.compiler.showWarnings=false "
                "-Dmaven.compiler.useIncrementalCompilation=false "
                "-Dmaven.compiler.failOnError=true -Dsurefire.skipAfterFailureCount=1 "
                "compiler:compile surefire:test "
                f"-Drat.skip=true -f {pom_file}; return 0\n"
            )
        elif tool.name.lower() in [
            "aprer",
            "repaircat",
            "repairllama",
            "arja",
            "arja_e",
            "tbar",
        ]:
            dock_file.write(
                "RUN mvn clean compile test "
                f"-Drat.skip=true -f {pom_file}; return 0\n"
            )

        for x in ["deps.sh", "install_deps"]:
            if os.path.exists(join(dir_info["local"]["setup"], x)):
                dock_file.write(
                    "RUN {1} bash {0} \n".format(
                        join(dir_info["container"]["setup"], x), prefix
                    )
                )

        # We assume that the container will always have the sh command available
        # This line is included against some issues with the container lifetime
        dock_file.write('ENTRYPOINT ["/bin/sh"]\n')
    return tmp_dockerfile


def _subject_based_image(
    bug_image_id: str,
    tool: AbstractTool,
    dir_info: DirectoryInfo,
    bug_info: Dict[str, Any],
    tag: Optional[str],
) -> str:
    dockerfile_name = "Dockerfile-{}-{}".format(bug_image_id, tool.name)
    if tag and tag != "":
        dockerfile_name += "-{}".format(tag)

    tmp_dockerfile = join(
        dir_info["local"]["setup"],
        dockerfile_name,
    )
    os.makedirs(dirname(tmp_dockerfile), exist_ok=True)
    with open(tmp_dockerfile, "w") as dock_file:
        dock_file.write("FROM {}\n".format(bug_image_id))
        dock_file.write("ADD . {0}\n".format(dir_info["container"]["setup"]))

        res, (output, error) = utilities.run_command(
            f"getent group {definitions.GROUP_NAME} | cut -d: -f3"
        )
        if not output or output.decode() == "":
            utilities.error_exit(
                f"Cannot the id of the group {definitions.GROUP_NAME}. Ensure that it exists"
            )

        group_id = output.decode().strip()

        emitter.debug(f"Group {definitions.GROUP_NAME} has id {group_id} ")
        prefix = ""
        if not tool.runs_as_root:
            prefix = "sudo"
            if tool.sudo_password:
                prefix = f'echo "{tool.sudo_password}\\n" | sudo -S'

        # Create a special group to ensure that files are accessible
        dock_file.write(
            f"RUN {prefix} bash -c 'groupadd -g {group_id} {definitions.GROUP_NAME}' \n"
        )

        # Make all user's primary group to be our special group
        dock_file.write(
            f'RUN {prefix} bash -c "cut -d: -f1 /etc/passwd | xargs -i usermod -g {definitions.GROUP_NAME} {{}} "\n'
        )

        ownership = ""
        if tool.image_user != "root":
            ownership = f"--chown={tool.image_user}:{definitions.GROUP_NAME}"

        for _dir in tool.portable_dirs:
            dock_file.write(
                "COPY --from={0} {2} {1} {1}\n".format(tool.image_name, _dir, ownership)
            )
        for _path in tool.path_to_binaries:
            dock_file.write('ENV PATH="$PATH:{0}"\n'.format(_path))
        # We assume that the container will always have the sh command available
        # This line is included against some issues with the container lifetime
        dock_file.write('ENTRYPOINT ["/bin/sh"]\n')
    return tmp_dockerfile


def construct_experiment_tool_image(
    bug_image_id: str,
    tool: AbstractTool,
    dir_info: DirectoryInfo,
    image_name: str,
    bug_info: Dict[str, Any],
    tag: Optional[str],
) -> str:
    if values.use_subject_as_base:
        tmp_dockerfile = _subject_based_image(
            bug_image_id, tool, dir_info, bug_info, tag
        )
    else:
        tmp_dockerfile = _tool_based_image(bug_image_id, tool, dir_info, bug_info, tag)
    id = container.build_image(tmp_dockerfile, image_name)
    os.remove(tmp_dockerfile)
    return id


def prepare_experiment_image(
    benchmark: AbstractBenchmark,
    bug_info: Dict[str, Any],
    cpu: List[str],
    gpu: List[str],
    tag: str,
    ignore_rebuild: bool = False,
) -> Optional[str]:
    utilities.check_space()
    bug_index = bug_info[definitions.KEY_ID]
    experiment_image_id = None
    if not values.use_container:
        if not values.use_valkyrie:
            is_error = benchmark.setup_experiment(bug_index, None, values.only_test)
            if is_error:
                return None
    else:
        bug_name = str(bug_info[definitions.KEY_BUG_ID])
        subject_name = str(bug_info[definitions.KEY_SUBJECT])
        # Allow for a special base setup folder if needed
        dir_setup_extended = (
            join(
                values.dir_benchmark,
                benchmark.name,
                subject_name,
                f"{bug_name}-{tag}",
                "",
            )
            if tag
            else None
        )
        benchmark.update_dir_info(
            generate_dir_info(
                benchmark.name, subject_name, bug_name, dir_setup_extended
            )
        )
        experiment_image_id = (
            benchmark.get_exp_image(
                bug_index, values.only_test, cpu, gpu, ignore_rebuild
            )
            if values.use_container
            else None
        )

    if not benchmark.pre_built:
        collect_benchmark_result(bug_info, benchmark)

    return experiment_image_id


def prepare_experiment_tool(
    bug_image_id: Optional[str],
    tool: AbstractTool,
    task_profile: Dict[str, Any],
    dir_info: DirectoryInfo,
    image_name: str,
    bug_info: Dict[str, Any],
    tag: Optional[str] = None,
) -> Optional[str]:
    if values.use_container and tool.locally_running:
        if not bug_image_id:
            utilities.error_exit("Bug image id not provided")
        emitter.information("\t\t[framework] preparing image {}".format(image_name))
        if (
            not container.image_exists(image_name)
            or values.rebuild_base
            or values.rebuild_all
        ):
            return construct_experiment_tool_image(
                bug_image_id, tool, dir_info, image_name, bug_info, tag
            )
        else:
            img = container.get_image(image_name)
            if not img:
                utilities.error_exit("Image exists yet was not found??")
            return cast(str, img.id)

    dir_local_patch = dir_info["local"]["patches"]
    config_patch_dir = task_profile.get(definitions.KEY_CONFIG_PATCH_DIR, None)
    if config_patch_dir == "setup":
        if not isdir(dir_local_patch):
            os.makedirs(dir_local_patch)
    else:
        if isdir(dir_local_patch):
            shutil.rmtree(dir_local_patch)
    return None
