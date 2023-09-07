import hashlib
import os
import time
from os.path import dirname
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
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
from app.core.task import repair
from app.core.task.typing import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool
from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool
from app.plugins import valkyrie


def update_dir_info(dir_info: DirectoryInfo, tool_name: str) -> DirectoryInfo:
    dir_info["local"]["instrumentation"] = join(
        dir_info["local"]["setup"], tool_name.lower()
    )
    dir_info["container"]["instrumentation"] = join(
        dir_info["container"]["setup"], tool_name.lower()
    )
    return dir_info


def generate_local_dir_info(benchmark_name: str, subject_name: str, bug_name: str):
    dir_path = join(benchmark_name, subject_name, bug_name, "")
    dir_exp_local = join(values.dir_experiments, dir_path)
    dir_setup_local = join(values.dir_main, "benchmark", dir_path)
    dir_aux_local = join(values.dir_benchmark, benchmark_name, subject_name, ".aux")
    dir_base_local = join(values.dir_benchmark, benchmark_name, subject_name, "base")
    dir_logs_local = join(values.dir_logs, dir_path)
    dir_artifact_local = join(values.dir_artifacts, dir_path)
    for directory in [dir_exp_local, dir_setup_local, dir_aux_local, dir_base_local]:
        if not os.path.isdir(directory):
            os.makedirs(directory, exist_ok=True)

    return {
        "logs": dir_logs_local,
        "artifacts": dir_artifact_local,
        "experiment": dir_exp_local,
        "setup": dir_setup_local,
        "base": dir_base_local,
        "aux": dir_aux_local,
    }


def generate_local_tool_dir_info(
    benchmark_name: str,
    subject_name: str,
    bug_name: str,
    hash: Any,
    tag_name: str,
):
    dir_name = f"{tag_name}-{hash.hexdigest()[:8]}"
    base_info = generate_local_dir_info(benchmark_name, subject_name, bug_name)

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
    benchmark_name: str, subject_name: str, bug_name: str, hash, tag_name: str
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_tool_dir_info(
            benchmark_name, subject_name, bug_name, hash, tag_name
        ),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info


def generate_dir_info(
    benchmark_name: str, subject_name: str, bug_name: str
) -> DirectoryInfo:
    dir_info: DirectoryInfo = {
        "local": generate_local_dir_info(benchmark_name, subject_name, bug_name),
        "container": generate_container_dir_info(
            benchmark_name, subject_name, bug_name
        ),
    }
    return dir_info


def construct_job_summary(job_identifier: str, results_summary: Any) -> str:
    json_f_name = f"experiment-summary-{job_identifier}.json"
    summary_f_path = join(values.dir_summaries, json_f_name)
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
    construct_job_summary(benchmark_tag_name, benchmark.stats.get_dict())


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
        task_tag_name, tool.stats.get_dict()
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
    cpu: str,
    container_config_info: Dict[str, Any],
    extra_volumes: Optional[Dict[str, Any]] = None,
) -> str:
    image_name = image_name.lower()
    container_id = container.get_container_id(container_name, ignore_not_found=True)
    if container_id:
        container.stop_container(container_id)
        container.remove_container(container_id)

    if not container.image_exists(image_name):
        utilities.error_exit("Image should be constructed by now!")

    volume_list = construct_container_volumes(dir_info, extra_volumes)

    extract_experiment_logs(
        dir_info, image_name, container_name, cpu, container_config_info
    )

    emitter.information("\t\t[framework] building main container for experiment")
    container_id = container.build_container(
        container_name, volume_list, image_name, cpu, container_config_info
    )
    if not container_id:
        utilities.error_exit("Container was not created successfully")
    return container_id


def extract_experiment_logs(
    dir_info: DirectoryInfo,
    image_name: str,
    container_name: str,
    cpu: str,
    container_config_info: Dict[str, Any],
):
    # Need to copy the logs from benchmark setup before instantiating the running container
    emitter.information(
        "\t\t[framework] building temporary container for log extraction"
    )

    tmp_container_id = container.get_container_id(container_name, ignore_not_found=True)

    if not tmp_container_id:
        tmp_container_id = container.build_container(
            container_name, dict(), image_name, cpu, container_config_info
        )

    if not tmp_container_id:
        utilities.error_exit("Could not create temporary container")
    else:
        container.copy_file_from_container(
            tmp_container_id, dir_info["container"]["logs"], dir_info["local"]["logs"]
        )
        if values.runs:
            container.stop_container(tmp_container_id)
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
    tag: Optional[str],
):
    dockerfile_name = "Dockerfile-{}-{}".format(repair_tool.name, bug_image_id)
    if tag:
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

        if os.path.exists(join(dir_info["local"]["setup"], "deps.sh")):
            dock_file.write(
                "RUN bash {0} || sudo bash {0} ; return 0".format(
                    join(dir_info["container"]["setup"], "deps.sh")
                )
            )
        if os.path.exists(join(dir_info["local"]["setup"], "install_deps")):
            dock_file.write(
                "RUN bash {0} || sudo bash {0} ; return 0".format(
                    join(dir_info["container"]["setup"], "install_deps")
                )
            )
    id = container.build_image(tmp_dockerfile, image_name)
    os.remove(tmp_dockerfile)
    return id


def prepare_experiment(
    benchmark: AbstractBenchmark,
    bug_info: Dict[str, Any],
    cpu: str,
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
        experiment_image_id = (
            benchmark.get_exp_image(bug_index, values.only_test, cpu)
            if values.use_container
            else None
        )

    if not benchmark.pre_built:
        collect_benchmark_result(bug_info, benchmark)

    return experiment_image_id


def prepare_experiment_tool(
    bug_image_id: str,
    repair_tool: AbstractTool,
    dir_info: DirectoryInfo,
    image_name: str,
    tag: Optional[str] = None,
):
    if values.use_container:
        if (
            not container.image_exists(image_name)
            or values.rebuild_base
            or values.rebuild_all
        ):
            return prepare_tool_experiment_image(
                bug_image_id, repair_tool, dir_info, image_name, tag
            )
    return None


def run(
    benchmark: AbstractBenchmark,
    tool: AbstractTool,
    bug_info: Dict[str, Any],
    task_config_info: Dict[str, Any],
    container_config_info: Dict[str, Any],
    task_identifier: str,
    cpu: str,
    task_image: Optional[str] = None,
):
    bug_name = str(bug_info[definitions.KEY_BUG_ID])
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    if definitions.KEY_CONFIG_TIMEOUT_TESTCASE in bug_info:
        task_config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = bug_info[
            definitions.KEY_CONFIG_TIMEOUT_TESTCASE
        ]

    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))

    dir_info = generate_tool_dir_info(
        benchmark.name, subject_name, bug_name, hash, task_identifier
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
        "\t\t[task profile] Fix-loc: {}".format(
            task_config_info[definitions.KEY_CONFIG_FIX_LOC]
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
