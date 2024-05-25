import copy
import hashlib
import os
import shutil
import time
from os.path import dirname
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import utilities
from app.core import values
from app.core import writer
from app.core.task import analyze
from app.core.task import fuzz
from app.core.task import localize
from app.core.task import repair
from app.core.task import select
from app.core.task import validate
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool
from app.drivers.tools.localize.AbstractLocalizeTool import AbstractLocalizeTool
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool
from app.drivers.tools.select.AbstractSelectTool import AbstractSelectTool
from app.drivers.tools.validate.AbstractValidateTool import AbstractValidateTool
from app.plugins import valkyrie


def update_dir_info(dir_info: DirectoryInfo, tool_name: str) -> DirectoryInfo:
    dir_info["local"]["instrumentation"] = join(
        dir_info["local"]["setup"], tool_name.lower()
    )
    dir_info["container"]["instrumentation"] = join(
        dir_info["container"]["setup"], tool_name.lower()
    )
    return dir_info


def generate_local_dir_info(
    benchmark_name: str, subject_name: str, bug_name: str, tag: str
):
    dir_path = join(benchmark_name, subject_name, bug_name, "")
    dir_exp_local = join(values.dir_experiments, dir_path)
    dir_setup_local = join(values.dir_benchmark, dir_path)

    dir_bugs_local = join(dir_setup_local, "bugs")
    dir_localization_local = join(dir_setup_local, "localization")
    dir_patches_local = join(dir_setup_local, "patches")
    dir_validation_local = join(dir_setup_local, "validation")
    dir_selection_local = join(dir_setup_local, "selection")

    dir_aux_local = join(values.dir_benchmark, benchmark_name, subject_name, ".aux")
    dir_base_local = join(values.dir_benchmark, benchmark_name, subject_name, "base")
    dir_logs_local = join(values.dir_logs, dir_path)
    dir_artifact_local = join(values.dir_artifacts, dir_path)
    for directory in [
        dir_exp_local,
        dir_setup_local,
        dir_aux_local,
        dir_base_local,
        dir_bugs_local,
        dir_patches_local,
        dir_localization_local,
        dir_validation_local,
        dir_selection_local,
    ]:
        if not os.path.isdir(directory):
            os.makedirs(directory, exist_ok=True)

    if tag:  # Allow for the usage of custom setup folders
        dir_path_extended = join(benchmark_name, subject_name, f"{bug_name}-{tag}", "")
        dir_setup_extended = join(values.dir_benchmark, dir_path_extended)
        if os.path.exists(dir_setup_extended):
            dir_setup_local = dir_setup_extended

    return {
        "logs": dir_logs_local,
        "artifacts": dir_artifact_local,
        "experiment": dir_exp_local,
        "setup": dir_setup_local,
        "base": dir_base_local,
        "aux": dir_aux_local,
        "patches": dir_patches_local,
        "localization": dir_localization_local,
        "selection": dir_selection_local,
        "validation": dir_validation_local,
        "bugs": dir_bugs_local,
    }


def generate_local_tool_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    hash: Any,
    task_identifier: str,
    tag: str,
):
    dir_name = f"{task_identifier}-{hash.hexdigest()[:8]}"
    base_info = generate_local_dir_info(benchmark_name, subject_name, bug_name, tag)

    dir_result_local = join(values.dir_results, dir_name)
    dir_log_local = join(values.dir_logs, dir_name)
    dir_artifact_local = join(values.dir_artifacts, dir_name)
    for directory in [dir_log_local, dir_result_local, dir_artifact_local]:
        os.makedirs(directory, exist_ok=True)

    base_info["logs"] = dir_log_local
    base_info["artifacts"] = dir_artifact_local
    base_info["results"] = dir_result_local

    return base_info


def generate_container_dir_info(benchmark_name: str, subject_name: str, bug_name: str):
    dir_path = join(benchmark_name, subject_name, bug_name, "")

    dir_setup_container = join("/setup", dir_path)
    dir_exp_container = join("/experiment", dir_path)
    dir_logs_container = "/logs"
    dir_artifact_container = "/output"
    dir_aux_container = join(dir_exp_container, ".aux")
    dir_base_container = join(dir_exp_container, "base")

    return {
        "logs": dir_logs_container,
        "artifacts": dir_artifact_container,
        "experiment": dir_exp_container,
        "setup": dir_setup_container,
        "base": dir_base_container,
        "aux": dir_aux_container,
    }


def generate_tool_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    hash,
    task_identifier: str,
    tag: str,
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_tool_dir_info(
            benchmark_name, subject_name, bug_name, hash, task_identifier, tag
        ),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info


def generate_dir_info(
    benchmark_name: str, subject_name: str, bug_name: str, tag: str
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_dir_info(benchmark_name, subject_name, bug_name, tag),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info


def construct_job_summary(
    job_identifier: str, dir: str, results_summary: Dict[str, Any]
) -> str:
    json_f_name = f"experiment-summary-{job_identifier}.json"
    summary_f_path = join(dir, json_f_name)
    writer.write_as_json(results_summary, summary_f_path)
    return summary_f_path


def collect_benchmark_result(
    bug_info: Dict[str, Any], benchmark: AbstractBenchmark
) -> None:
    emitter.normal("\t\t[framework] collecting benchmark results")
    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))
    bug_id = str(bug_info[definitions.KEY_BUG_ID])
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    benchmark_tag_name = "{}-{}-{}-{}".format(
        benchmark.name, subject_name, bug_id, hash.hexdigest()[:8]
    )
    benchmark.print_stats()
    logger.log_benchmark_stats(benchmark_tag_name, benchmark.stats)
    construct_job_summary(
        benchmark_tag_name, values.dir_summaries_benchmarks, benchmark.stats.get_dict()
    )


def collect_tool_result(dir_info: DirectoryInfo, experiment_info, tool: AbstractTool):
    emitter.normal("\t\t[framework] collecting experiment results")
    task_tag_name = dir_info["local"]["logs"].split("/")[-1]
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info.get(definitions.KEY_FAILING_TEST, [])
    tool.analyse_output(dir_info, bug_id, failing_test_list)
    tool.print_stats()
    tool.log_output_path = ""
    logger.log_tool_stats(task_tag_name, tool.stats)
    dir_info["local"]["summary"] = construct_job_summary(
        task_tag_name, values.dir_summaries_tools, tool.stats.get_dict()
    )
    if values.use_valkyrie:
        patch_dir = join(dir_info["local"]["artifacts"], "patches")
        valkyrie.analyse_output(patch_dir, tool.stats)


def retrieve_results(archive_name: str, tool: AbstractTool) -> bool:
    emitter.normal("\t\tretrieving results")
    archive_path = join(values.dir_main, "results", tool.name.lower(), archive_name)
    if os.path.isfile(archive_path):
        extract_command = "cp {} {};".format(archive_path, values.dir_results)
        extract_command += "cd {};".format(values.dir_results)
        extract_command += "tar -xf {}" + archive_name
        utilities.execute_command(extract_command)
        return True
    else:
        emitter.error("\t\t[error] Result archive not found at {}".format(archive_path))
        return False


def save_artifacts(dir_info: DirectoryInfo, tool: AbstractTool) -> None:
    emitter.normal(
        "\t\t[framework] Saving artifacts from tool {} and cleaning up".format(
            tool.name
        )
    )
    local_info = dir_info["local"]
    dir_results = local_info["results"]
    os.makedirs(dir_results, exist_ok=True)
    tool.save_artifacts(local_info)
    tool.post_process()
    save_command = "cp -f {} {};".format(values.file_main_log, dir_results)
    save_command += "cp -f {}/* {}".format(values.file_error_log, dir_results)
    utilities.execute_command(save_command)


def create_running_container(
    dir_info: DirectoryInfo,
    image_name: str,
    container_name: str,
    cpu: List[str],
    gpu: List[str],
    container_config_info: Dict[str, Any],
    extra_volumes: Optional[Dict[str, Any]] = None,
) -> str:
    image_name = image_name.lower()
    emitter.information(
        "\t\t[framework] Creating running container with image {}".format(image_name)
    )
    container_id = container.get_container_id(container_name, ignore_not_found=True)
    if container_id:
        container.kill_container(container_id, ignore_errors=True)
        container.remove_container(container_id)

    if not container.image_exists(image_name):
        utilities.error_exit("Image should be constructed by now!")

    volume_list = construct_container_volumes(dir_info, extra_volumes)

    extract_experiment_logs(
        dir_info, image_name, container_name, cpu, gpu, container_config_info
    )

    emitter.information("\t\t[framework] building main container for experiment")
    is_network_enabled = True
    if container_config_info:
        is_network_enabled = container_config_info.get(
            definitions.KEY_CONTAINER_ENABLE_NETWORK, True
        )
    container_id = container.build_container(
        container_name,
        volume_list,
        image_name,
        cpu,
        gpu,
        container_config_info,
        not is_network_enabled,
    )
    if not container_id:
        utilities.error_exit("Container was not created successfully")
    return container_id


def extract_experiment_logs(
    dir_info: DirectoryInfo,
    image_name: str,
    container_name: str,
    cpu: List[str],
    gpu: List[str],
    container_config_info: Dict[str, Any],
):
    # Need to copy the logs from benchmark setup before instantiating the running container
    emitter.information(
        "\t\t[framework] building temporary container for log extraction"
    )

    tmp_container_id = container.get_container_id(container_name, ignore_not_found=True)

    if not tmp_container_id:
        tmp_container_id = container.build_container(
            container_name, dict(), image_name, cpu, gpu, container_config_info
        )

    if not tmp_container_id:
        utilities.error_exit("Could not create temporary container")
    else:
        container.copy_file_from_container(
            tmp_container_id, dir_info["container"]["logs"], dir_info["local"]["logs"]
        )
        if values.runs:
            container.stop_container(tmp_container_id, 5)
            container.remove_container(tmp_container_id)


def construct_container_volumes(
    dir_info: DirectoryInfo, extra_volumes: Optional[Dict[str, Any]] = None
):
    volume_list = {
        # dir_exp_local: {'bind': '/experiment', 'mode': 'rw'},
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


def prepare_tool_experiment_image(
    bug_image_id: str,
    repair_tool: AbstractTool,
    dir_info: DirectoryInfo,
    image_name: str,
    bug_info: Dict[str, Any],
    tag: Optional[str],
):
    dockerfile_name = "Dockerfile-{}-{}".format(repair_tool.name, bug_image_id)
    if tag and tag != "":
        dockerfile_name += "-{}".format(tag)

    tmp_dockerfile = join(
        dir_info["local"]["setup"],
        dockerfile_name,
    )
    os.makedirs(dirname(tmp_dockerfile), exist_ok=True)
    with open(tmp_dockerfile, "w") as dock_file:
        dock_file.write("FROM {}\n".format(repair_tool.image_name))
        dock_file.write("ADD . {0}\n".format(dir_info["container"]["setup"]))
        dock_file.write("COPY --from={0} {1} {1}\n".format(bug_image_id, "/experiment"))
        dock_file.write("COPY --from={0} {1} {1}\n".format(bug_image_id, "/logs"))
        dock_file.write("COPY --from={0} {1} {1}\n".format(bug_image_id, "/root/"))

        src_dir = bug_info.get(
            definitions.KEY_SOURCE_DIRECTORY,
            join(dir_info["container"]["experiment"], "src"),
        )
        if str(src_dir)[-1] == "/":
            src_dir = src_dir[:-1]
        pom_dir = os.path.dirname(os.path.dirname(os.path.dirname(src_dir))) or "."
        pom_file = f"{dir_info['container']['experiment']}/src/{pom_dir}/pom.xml"
        if repair_tool.name.lower() in ["et", "grt5"]:
            dock_file.write(
                "RUN mvnd -1 -B -Dmvnd.daemonStorage=/root/workflow/default "
                "-ff -Djava.awt.headless=true -Dmaven.compiler.showWarnings=false "
                "-Dmaven.compiler.useIncrementalCompilation=false "
                "-Dmaven.compiler.failOnError=true -Dsurefire.skipAfterFailureCount=1 "
                "compiler:compile surefire:test "
                f"-Drat.skip=true -f {pom_file}; return 0\n"
            )
        elif repair_tool.name.lower() in [
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

        if os.path.exists(join(dir_info["local"]["setup"], "deps.sh")):
            dock_file.write(
                "RUN bash {0} || sudo bash {0} \n".format(
                    join(dir_info["container"]["setup"], "deps.sh")
                )
            )
        if os.path.exists(join(dir_info["local"]["setup"], "install_deps")):
            dock_file.write(
                "RUN bash {0} || sudo bash {0} \n".format(
                    join(dir_info["container"]["setup"], "install_deps")
                )
            )
        # We assume that the container will always have the sh command available
        # This line is included against some issues with the container lifetime
        dock_file.write('ENTRYPOINT ["/bin/sh"]\n')
    id = container.build_image(tmp_dockerfile, image_name)
    os.remove(tmp_dockerfile)
    return id


def prepare_experiment(
    benchmark: AbstractBenchmark,
    bug_info: Dict[str, Any],
    cpu: List[str],
    gpu: List[str],
    tag: str,
    ignore_rebuild: bool = False,
):
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
        benchmark.update_dir_info(
            generate_dir_info(benchmark.name, subject_name, bug_name, tag)
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
    repair_tool: AbstractTool,
    task_profile: Dict[str, Any],
    dir_info: DirectoryInfo,
    image_name: str,
    bug_info: Dict[str, Any],
    tag: Optional[str] = None,
):
    if values.use_container:
        if not bug_image_id:
            utilities.error_exit("Bug image id not provided")
        emitter.information("\t\t[framework] preparing image {}".format(image_name))
        if (
            not container.image_exists(image_name)
            or values.rebuild_base
            or values.rebuild_all
        ):
            return prepare_tool_experiment_image(
                bug_image_id, repair_tool, dir_info, image_name, bug_info, tag
            )
        else:
            img = container.get_image(image_name)
            if not img:
                utilities.error_exit("Image exists yet was not found??")
            return cast(str, img.id)

    dir_local_patch = dir_info["local"]["patches"]
    config_patch_dir = task_profile.get(definitions.KEY_CONFIG_PATCH_DIR, None)
    if config_patch_dir == "setup":
        if not os.path.isdir(dir_local_patch):
            os.makedirs(dir_local_patch)
    else:
        if os.path.isdir(dir_local_patch):
            shutil.rmtree(dir_local_patch)
    return None


def run(
    benchmark: AbstractBenchmark,
    tool: AbstractTool,
    bug_info: Dict[str, Any],
    task_config_info_template: Dict[str, Any],
    container_config_info: Dict[str, Any],
    task_identifier: str,
    cpu: List[str],
    gpu: List[str],
    task_image: Optional[str] = None,
):
    bug_name = str(bug_info[definitions.KEY_BUG_ID])
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    task_config_info = copy.deepcopy(task_config_info_template)

    task_config_info[definitions.KEY_GPUS] = gpu
    task_config_info[definitions.KEY_CPUS] = cpu

    if definitions.KEY_CONFIG_TIMEOUT_TESTCASE in bug_info:
        task_config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = bug_info[
            definitions.KEY_CONFIG_TIMEOUT_TESTCASE
        ]

    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))

    dir_info = generate_tool_dir_info(
        benchmark.name,
        subject_name,
        bug_name,
        hash,
        task_identifier,
        task_config_info.get(definitions.KEY_TOOL_TAG, ""),
    )
    benchmark.update_dir_info(dir_info)
    print_task_info(
        task_config_info, container_config_info, bug_name, subject_name, dir_info
    )

    dir_info = update_dir_info(dir_info, tool.name)
    dir_instr_local = dir_info["local"]["instrumentation"]
    dir_result_local = dir_info["local"]["results"]

    container_id = None
    # emitter.information("directory is {}".format(dir_instr_local))
    if os.path.isdir(dir_instr_local):
        emitter.information(
            "\t\t[framework] there is custom instrumentation for {}".format(tool.name)
        )

    if values.only_analyse:
        can_analyse_results = True
        if (
            not os.path.isdir(dir_result_local)
            or len(os.listdir(dir_result_local)) == 0
        ):
            archive_name = task_identifier + ".tar.gz"
            can_analyse_results = retrieve_results(archive_name, tool)
        if can_analyse_results:
            collect_tool_result(dir_info, bug_info, tool)
    else:
        utilities.clean_artifacts(dir_info["local"]["artifacts"])
        utilities.clean_artifacts(dir_info["local"]["logs"])
        benchmark.update_dir_info(dir_info)

        if values.use_container:
            if tool.image_name is None:
                utilities.error_exit(
                    "Repair tool does not have a docker image name assigned: {}".format(
                        tool.name
                    )
                )

            if task_image is None:
                utilities.error_exit(
                    "No task image provided, though container mode is selected"
                )

            container_id = create_running_container(
                dir_info,
                task_image,
                task_identifier,
                cpu,
                gpu,
                container_config_info,
                tool.bindings,
            )
            if not container_id:
                utilities.error_exit("Could not get container id!")

    if not values.only_setup:
        task_type = values.task_type.get()
        if task_type == "repair":
            repair.repair_all(
                dir_info,
                bug_info,
                cast(AbstractRepairTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "analyze":
            analyze.analyze_all(
                dir_info,
                bug_info,
                cast(AbstractAnalyzeTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "fuzz":
            fuzz.fuzz_all(
                dir_info,
                bug_info,
                cast(AbstractFuzzTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "validate":
            validate.validate_all(
                dir_info,
                bug_info,
                cast(AbstractValidateTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "localize":
            localize.localize_all(
                dir_info,
                bug_info,
                cast(AbstractLocalizeTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "select":
            select.select_all(
                dir_info,
                bug_info,
                cast(AbstractSelectTool, tool),
                task_config_info,
                container_id,
                benchmark.name,
            )
        elif task_type == "composite":
            pass
        else:
            utilities.error_exit(f"Unknown task type: {task_type}")

        # update container stats
        if values.use_container:
            if not container_id:
                utilities.error_exit("Use container but ID is none?")
            tool.update_container_stats(container_id)

        if not values.only_instrument:
            collect_tool_result(dir_info, bug_info, tool)
            save_artifacts(dir_info, tool)
            dir_archive = join(values.dir_results, tool.name)
            dir_result = dir_info["local"]["results"]
            utilities.archive_results(dir_result, dir_archive)
            if values.compact_results:
                utilities.clean_artifacts(dir_result)

        if values.use_container and tool.container_id:
            container.stop_container(tool.container_id)

    return dir_info


def print_task_info(
    task_config_info: Dict[str, Any],
    container_config_info: Dict[str, Any],
    bug_name: str,
    subject_name: str,
    dir_info: DirectoryInfo,
):
    emitter.highlight(
        "\t\t[task profile] Identifier: {}".format(task_config_info[definitions.KEY_ID])
    )
    emitter.highlight(
        "\t\t[task profile] Timeout: {}".format(
            task_config_info[definitions.KEY_CONFIG_TIMEOUT]
        )
    )
    emitter.highlight(
        "\t\t[task profile] Fix-Loc: {}".format(
            task_config_info[definitions.KEY_CONFIG_FIX_LOC]
        )
    )
    emitter.highlight(
        "\t\t[task profile] Patch-Dir: {}".format(
            task_config_info.get(definitions.KEY_CONFIG_PATCH_DIR, None)
        )
    )
    emitter.highlight(
        "\t\t[task profile] Test-suite ratio: {}".format(
            task_config_info[definitions.KEY_CONFIG_TEST_RATIO]
        )
    )

    if values.use_container:
        emitter.highlight(
            "\t\t[container profile] Identifier: {}".format(
                container_config_info[definitions.KEY_ID]
            )
        )

        emitter.highlight(
            "\t\t[container profile] CPU Count: {}".format(
                container_config_info[definitions.KEY_CONTAINER_CPU_COUNT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] GPU Count: {}".format(
                container_config_info[definitions.KEY_CONTAINER_GPU_COUNT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] RAM Limit: {}".format(
                container_config_info[definitions.KEY_CONTAINER_MEM_LIMIT]
            )
        )

        emitter.highlight(
            "\t\t[container profile] Enable Network: {}".format(
                container_config_info[definitions.KEY_CONTAINER_ENABLE_NETWORK]
            )
        )

    emitter.highlight("\t\t[meta-data] Project: {}".format(subject_name))
    emitter.highlight("\t\t[meta-data] Bug ID: {}".format(bug_name))
    emitter.highlight(
        "\t\t[meta-data] Logs directory: {}".format(dir_info["local"]["logs"])
    )
    emitter.highlight(
        "\t\t[meta-data] Output directory: {}".format(dir_info["local"]["artifacts"])
    )
    emitter.highlight(
        "\t\t[meta-data] Summary directory: {}".format(values.dir_summaries)
    )
