import hashlib
import os
import threading
import time
from os.path import abspath
from os.path import dirname
from os.path import join
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional

from app.core import analyze
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import repair
from app.core import ui
from app.core import utilities
from app.core import values
from app.core import writer
from app.core.stats import ErrorStats
from app.core.stats import SpaceStats
from app.core.stats import TimeStats
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.drivers.tools.analyze.AbstractAnalyzeTool import AbstractAnalyzeTool
from app.drivers.tools.repair.AbstractRepairTool import AbstractRepairTool
from app.plugins import valkyrie


def update_dir_info(dir_info: Dict[str, Dict[str, str]], tool_name: str):
    dir_setup_local = dir_info["local"]["setup"]
    dir_setup_container = dir_info["container"]["setup"]
    dir_instrumentation_local = join(dir_setup_local, str(tool_name).lower())
    dir_instrumentation_container = join(dir_setup_container, str(tool_name).lower())
    dir_info["local"]["instrumentation"] = dir_instrumentation_local
    dir_info["container"]["instrumentation"] = dir_instrumentation_container
    return dir_info


def generate_dir_info(
    benchmark_name: str, subject_name: str, bug_name: str, tag_name: str
):
    dir_path = join(benchmark_name, subject_name, bug_name, "")
    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))
    dir_name = f"{tag_name}-{hash.hexdigest()[:8]}"
    dir_setup_container = join("/setup", dir_path)
    dir_exp_container = join("/experiment", dir_path)
    dir_logs_container = "/logs"
    dir_artifact_container = "/output"
    dir_setup_local = join(values.dir_main, "benchmark", dir_path)
    dir_exp_local = join(values.dir_experiments, dir_path)
    dir_result_local = join(values.dir_results, dir_name)
    dir_log_local = join(values.dir_logs, dir_name)
    dir_artifact_local = join(values.dir_artifacts, dir_name)

    for directory in [dir_log_local, dir_result_local, dir_exp_local]:
        if not os.path.isdir(directory):
            os.makedirs(directory)

    dir_aux_local = join(values.dir_benchmark, benchmark_name, subject_name, ".aux")
    dir_aux_container = join(dir_exp_container, ".aux")
    dir_base_local = join(values.dir_benchmark, benchmark_name, subject_name, "base")

    dir_base_container = join(dir_exp_container, "base")

    dir_info_local = {
        "logs": dir_log_local,
        "artifacts": dir_artifact_local,
        "results": dir_result_local,
        "experiment": dir_exp_local,
        "setup": dir_setup_local,
        "base": dir_base_local,
        "aux": dir_aux_local,
    }

    dir_info_container = {
        "logs": dir_logs_container,
        "artifacts": dir_artifact_container,
        "experiment": dir_exp_container,
        "setup": dir_setup_container,
        "base": dir_base_container,
        "aux": dir_aux_container,
    }

    dir_info = {"local": dir_info_local, "container": dir_info_container}
    return dir_info


def archive_results(dir_results: str, dir_archive: str):
    for output_dir in [dir_results, dir_archive]:
        if not os.path.isdir(output_dir):
            os.makedirs(output_dir)

    experiment_id = dir_results.split("/")[-1]

    archive_command = (
        "cd {res} ; tar cvzf {id}.tar.gz {id} ; mv {id}.tar.gz {arc}".format(
            res=dirname(abspath(dir_results)), id=experiment_id, arc=dir_archive
        )
    )

    utilities.execute_command(archive_command)


def analyse_result(dir_info_list, experiment_info, tool_list: List[AbstractTool]):
    emitter.normal("\t\t(framework) analysing experiment results")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    first_start = None
    patch_dir = None
    for dir_info, tool in zip(dir_info_list, tool_list):
        space_info: SpaceStats
        time_info: TimeStats
        error_info: ErrorStats
        space_info, time_info, error_info = tool.analyse_output(
            dir_info, bug_id, failing_test_list
        )
        conf_id = str(values.current_profile_id.get("NA"))
        exp_id = conf_id + "-" + bug_id
        values.stats_results[exp_id] = (space_info, time_info)
        tool.print_stats(space_info, time_info)
        tool.log_output_path = ""
        logger.log_stats(exp_id)
        dir_output = dir_info["local"]["artifacts"]
        patch_dir = dir_output + "/patches"
        if values.use_valkyrie:
            valkyrie.analyse_output(patch_dir, time_info)
            break


def retrieve_results(archive_name, tool: AbstractTool):
    emitter.normal("\t\tretrieving results")
    archive_path = join(values.dir_main, "results", tool.name.lower(), archive_name)
    if os.path.isfile(archive_path):
        extract_command = "cp {} {};".format(archive_path, values.dir_results)
        extract_command += "cd {};".format(values.dir_results)
        extract_command += "tar -xf {}" + archive_name
        utilities.execute_command(extract_command)
        return True
    else:
        emitter.error("\t\t(error) result archive not found at " + archive_path)
        return False


def save_artifacts(dir_info_list, experiment_info, tool_list, container_id_list):
    emitter.normal("\t\t(framework) saving artifacts and cleaning up")
    for dir_info_entry, container_id, tool in zip(
        dir_info_list, container_id_list, tool_list
    ):
        dir_info = dir_info_entry["local"]
        # dir_expr = dir_info["experiment"]
        # dir_artifacts = dir_info["artifacts"]
        dir_results = dir_info["results"]
        if not os.path.isdir(dir_results):
            os.system("mkdir -p {}".format(dir_results))
        tool.save_artifacts(dir_info)
        tool.post_process()
        save_command = "cp -f {} {};".format(values.file_main_log, dir_results)
        save_command += "cp -f {}/* {}".format(values.file_error_log, dir_results)
        utilities.execute_command(save_command)


def create_running_container(
    bug_image_id: str,
    repair_tool: AbstractTool,
    dir_info: Dict[str, Dict[str, str]],
    container_name: str,
    cpu: str,
):
    container_id = container.get_container_id(container_name)
    if container_id:
        container.stop_container(container_id)
        container.remove_container(container_id)
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
    if (
        not container.image_exists(container_name.lower())
        or values.rebuild_base
        or values.rebuild_all
    ):
        tmp_dockerfile = "{}/Dockerfile-{}-{}".format(
            dir_info["local"]["setup"], repair_tool.name, bug_image_id
        )
        with open(tmp_dockerfile, "w") as dock_file:
            dock_file.write("FROM {}\n".format(repair_tool.image_name))
            dock_file.write("ADD . {0}\n".format(dir_info["container"]["setup"]))
            dock_file.write(
                "COPY --from={0} {1} {1}\n".format(bug_image_id, "/experiment")
            )
            dock_file.write("COPY --from={0} {1} {1}\n".format(bug_image_id, "/logs"))
            dock_file.write(
                "RUN bash {0} || sudo bash {0} ; return 0".format(
                    join(dir_info["container"]["setup"], "deps.sh")
                )
            )
        container.build_image(tmp_dockerfile, container_name.lower())
        os.remove(tmp_dockerfile)
    # Need to copy the logs from benchmark setup before instantiating the running container
    tmp_container_id = container.build_container(
        container_name, dict(), container_name.lower(), cpu
    )
    if not tmp_container_id:
        utilities.error_exit("Could not create temporary container")
    else:
        copy_log_cmd = "docker cp {}:{} {}".format(
            tmp_container_id, dir_info["container"]["logs"], dir_info["local"]["logs"]
        )
        utilities.execute_command(copy_log_cmd)
        container.stop_container(tmp_container_id)
        container.remove_container(tmp_container_id)
    container_id = container.build_container(
        container_name, volume_list, container_name.lower(), cpu
    )
    return container_id


def construct_summary():
    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))
    json_f_name = f"experiment-summary-{hash.hexdigest()[:8]}.json"
    summary_f_path = f"{values.dir_summaries}/{json_f_name}"
    results_summary = dict()
    for exp_id in values.stats_results:
        space_info, time_info = values.stats_results[exp_id]
        results_summary[exp_id] = {
            "space": space_info.get_array(),
            "time": time_info.get_array(),
        }
    writer.write_as_json(results_summary, summary_f_path)


def run(
    benchmark: AbstractBenchmark,
    tool_list: List[AbstractTool],
    bug_info: Dict[str, Any],
    config_info: Dict[str, Any],
    run_identifier: str,
    cpu: str,
):
    dir_info_list = []
    container_id_list: List[str] = []
    bug_index = bug_info[definitions.KEY_ID]
    bug_name = str(bug_info[definitions.KEY_BUG_ID])
    config_id = config_info[definitions.KEY_ID]
    if definitions.KEY_CONFIG_TIMEOUT_TESTCASE in bug_info:
        config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = bug_info[
            definitions.KEY_CONFIG_TIMEOUT_TESTCASE
        ]
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    tag_name = "-".join(
        [config_id]
        + list(map(lambda x: x.name, tool_list))
        + [benchmark.name, subject_name, bug_name]
    )
    dir_info = generate_dir_info(benchmark.name, subject_name, bug_name, tag_name)
    emitter.highlight("\t(profile) identifier: " + str(config_info[definitions.KEY_ID]))
    emitter.highlight(
        "\t[profile] timeout: " + str(config_info[definitions.KEY_CONFIG_TIMEOUT])
    )
    emitter.highlight(
        "\t[profile] fix-loc: " + config_info[definitions.KEY_CONFIG_FIX_LOC]
    )
    emitter.highlight(
        "\t[profile] test-suite ratio: "
        + str(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    )
    emitter.highlight("\t(meta-data) project: {}".format(subject_name))
    emitter.highlight("\t(meta-data) bug ID: {}".format(bug_name))
    emitter.highlight(
        "\t[meta-data] logs directory: {}".format(dir_info["local"]["logs"])
    )
    emitter.highlight(
        "\t[meta-data] output directory: {}".format(dir_info["local"]["artifacts"])
    )
    exp_img_id = None

    benchmark.update_dir_info(dir_info)
    if values.use_container:
        exp_img_id = benchmark.get_exp_image(bug_index, values.only_test, cpu)
    else:
        if not values.use_valkyrie:
            benchmark.setup_experiment(bug_index, None, values.only_test)

    for index, repair_tool in enumerate(tool_list):
        container_id = None
        tool_name = repair_tool.name if len(tool_list) <= 1 else "multi"
        dir_info = update_dir_info(dir_info, tool_name)
        dir_instr_local = dir_info["local"]["instrumentation"]
        dir_result_local = dir_info["local"]["results"]
        # emitter.information("directory is {}".format(dir_instr_local))
        if os.path.isdir(dir_instr_local):
            emitter.warning(
                "\t\t[note] there is custom instrumentation for " + repair_tool.name
            )
        if values.only_analyse:
            if (
                not os.path.isdir(dir_result_local)
                or len(os.listdir(dir_result_local)) == 0
            ):
                archive_name = (
                    "-".join(
                        [
                            config_id,
                            benchmark.name,
                            repair_tool.name,
                            subject_name,
                            bug_name,
                        ]
                    )
                    + ".tar.gz"
                )
                if not retrieve_results(archive_name, repair_tool):
                    continue
            analyse_result(dir_info, bug_info, [repair_tool])
            continue
        if index == 0:
            dir_output_local = dir_info["local"]["artifacts"]
            dir_logs_local = dir_info["local"]["logs"]
            utilities.clean_artifacts(dir_output_local)
            utilities.clean_artifacts(dir_logs_local)
        benchmark.update_dir_info(dir_info)
        if values.use_container and exp_img_id:
            container_name = "{}-{}-{}-{}".format(
                tool_name, benchmark.name, subject_name, bug_name
            )
            if repair_tool.image_name is None:
                utilities.error_exit(
                    "Repair tool does not have a Dockerfile: {}".format(
                        repair_tool.name
                    )
                )

            container_id = create_running_container(
                exp_img_id, repair_tool, dir_info, container_name, cpu
            )
        if container_id:
            container_id_list.append(container_id)
        else:
            utilities.error_exit("Could not get container id!")
        dir_info_list.append(dir_info)

    if not values.only_setup:
        task_type = values.task_type
        if values.task_type == "repair":
            repair.repair_all(
                dir_info_list,
                bug_info,
                cast(List[AbstractRepairTool], tool_list),
                config_info,
                container_id_list,
                benchmark.name,
            )
        elif values.task_type == "analyze":
            analyze.analyze_all(
                dir_info_list,
                bug_info,
                cast(List[AbstractAnalyzeTool], tool_list),
                config_info,
                container_id_list,
                benchmark.name,
            )
        else:
            utilities.error_exit(f"Unknown task type: {task_type}")
        if not values.only_instrument:
            analyse_result(dir_info_list, bug_info, tool_list)
            save_artifacts(dir_info_list, bug_info, tool_list, container_id_list)
            tool_name = tool_list[0].name
            if len(tool_list) > 1:
                tool_name = "multi"
            dir_archive = join(values.dir_results, tool_name)
            dir_result = dir_info_list[0]["local"]["results"]
            archive_results(dir_result, dir_archive)
            utilities.clean_artifacts(dir_result)

    construct_summary()
    if values.ui_active:
        ui.get_ui().post_message(
            ui.JobFinish(run_identifier, ui.JobFinish.Status.SUCCESS)
        )
