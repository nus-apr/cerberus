import hashlib
import os
import threading
import time
from os.path import dirname, abspath, join

from app.core import (
    emitter,
    logger,
    definitions,
    values,
    container,
    parallel,
    utilities
)
from app.drivers.tools import AbstractTool
from app.plugins import valkyrie



def update_dir_info(dir_info, tool_name):
    dir_setup_local = dir_info["local"]["setup"]
    dir_setup_container = dir_info["container"]["setup"]
    dir_instrumentation_local = join(dir_setup_local, str(tool_name).lower())
    dir_instrumentation_container = join(dir_setup_container, str(tool_name).lower())
    dir_info["local"]["instrumentation"] = dir_instrumentation_local
    dir_info["container"]["instrumentation"] = dir_instrumentation_container
    return dir_info


def generate_dir_info(benchmark_name, subject_name, bug_name, link_name):
    dir_path = join(benchmark_name, subject_name, bug_name) + "/"
    hash = hashlib.sha1()
    hash.update(str(time.time()).encode("utf-8"))
    dir_name = hash.hexdigest()
    dir_setup_container = join("/setup", dir_path)
    dir_exp_container = join("/experiment", dir_path)
    dir_logs_container = "/logs"
    dir_artifact_container = "/output"
    dir_setup_local = values.dir_main + "/benchmark/" + dir_path
    dir_exp_local = values.dir_experiments + "/" + dir_path
    dir_result_local = values.dir_results + "/" + dir_name
    dir_log_local = values.dir_logs + "/" + dir_name
    dir_artifact_local = values.dir_artifacts + "/" + dir_name
    if not os.path.isdir(dir_log_local):
        os.makedirs(dir_log_local)
    if not os.path.isdir(dir_result_local):
        os.makedirs(dir_result_local)
    if not os.path.isdir(dir_exp_local):
        os.makedirs(dir_exp_local)

    dir_aux_local = (
        values.dir_benchmark + "/" + benchmark_name + "/" + subject_name + "/.aux"
    )
    dir_aux_container = dir_exp_container + "/.aux"
    dir_base_local = (
        values.dir_benchmark + "/" + benchmark_name + "/" + subject_name + "/base"
    )

    dir_base_container = join(dir_exp_container + "base")

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


def archive_results(dir_results, dir_archive):
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


def repair(
    dir_info,
    experiment_info,
    tool: AbstractTool,
    config_info,
    container_id,
    benchmark_name,
):
    fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])
    fix_line_numbers = [str(x) for x in experiment_info[definitions.KEY_FIX_LINES]]
    experiment_info[definitions.KEY_FIX_LINES] = fix_line_numbers
    experiment_info[definitions.KEY_BENCHMARK] = benchmark_name
    fix_location = None
    if config_info[definitions.KEY_CONFIG_FIX_LOC] == "dev":
        fix_location = fix_source_file + ":" + ",".join(fix_line_numbers)
    experiment_info[definitions.KEY_FIX_LOC] = fix_location
    test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
    test_timeout = int(config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE])
    passing_id_list_str = experiment_info[definitions.KEY_PASSING_TEST]
    passing_test_list = []
    if str(passing_id_list_str).replace(",", "").isnumeric():
        passing_test_list = passing_id_list_str.split(",")
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    experiment_info[definitions.KEY_PASSING_TEST] = passing_test_list[
        : int(len(passing_test_list) * test_ratio)
    ]
    if isinstance(failing_test_list, str):
        failing_test_list = failing_test_list.split(",")
    experiment_info[definitions.KEY_FAILING_TEST] = failing_test_list
    experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = test_timeout
    config_info[definitions.KEY_TOOL_PARAMS] = values.tool_params
    tool.update_info(container_id, values.only_instrument, dir_info)
    tool.repair(experiment_info, config_info)


def setup_for_valkyrie(dir_info, container_id, bug_info, benchmark_name):
    dir_output_local = dir_info["local"]["artifacts"]
    if container_id:
        dir_expr = dir_info["container"]["experiment"]
    else:
        dir_expr = dir_info["local"]["experiment"]
    binary_path_rel = bug_info.get(definitions.KEY_BINARY_PATH,"")
    valkyrie_binary_path = join(dir_output_local, "binary")
    binary_path = join(dir_expr, "src", binary_path_rel)
    if container_id:
        copy_command = "docker cp {}:{} {}".format(
            container_id, binary_path, valkyrie_binary_path
        )
    else:
        copy_command = "cp {} {} ;".format(binary_path, valkyrie_binary_path)

    utilities.execute_command(copy_command)
    values.LIST_PROCESSED = []
    subject_name = bug_info[definitions.KEY_SUBJECT]
    bug_id = str(bug_info[definitions.KEY_BUG_ID])

    test_driver_path = values.dir_main + "/benchmark/{}/{}/{}/test.sh".format(
        benchmark_name, subject_name, bug_id
    )
    test_dir_path = values.dir_main + "/benchmark/{}/{}/{}/tests".format(
        benchmark_name, subject_name, bug_id
    )
    test_suite_path = values.dir_main + "/benchmark/{}/{}/{}/test-suite".format(
        benchmark_name, subject_name, bug_id
    )
    oracle_path = values.dir_main + "/benchmark/{}/{}/{}/oracle*".format(
        benchmark_name, subject_name, bug_id
    )
    valkyrie_oracle_path = dir_output_local + "/oracle"
    if not os.path.isdir(test_suite_path):
        if os.path.isfile(valkyrie_oracle_path):
            os.remove(valkyrie_oracle_path)
        with open(valkyrie_oracle_path, "w") as oracle_file:
            oracle_file.writelines("#!/bin/bash\n")
            oracle_file.writelines(
                'script_dir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"\n'
            )
            oracle_file.writelines("export LD_LIBRARY_PATH=$script_dir/../../../libs\n")
            oracle_file.writelines("$script_dir/test.sh /dev/null $@\n")
        os.system("chmod +x {}".format(valkyrie_oracle_path))
        copy_command = "cp {} {} ; ".format(test_driver_path, dir_output_local)
        copy_command += "cp -rf {} {} ; ".format(test_dir_path, dir_output_local)
        copy_command += "cp -rf {} {}".format(oracle_path, dir_output_local)
    else:
        copy_command = "cp -rf {} {}".format(test_suite_path, dir_output_local)
        file_list = list()
        for (dir_path, dir_names, file_names) in os.walk(test_suite_path):
            file_list += [os.path.join(dir_path, file) for file in file_names]

        for binary_file in file_list:
            if ".orig" in binary_file:
                os.system(
                    "e9afl {} -o {} > /dev/null 2>&1".format(
                        binary_file, binary_file.replace(".orig", ".inst_coverage")
                    )
                )
        valkyrie_oracle_path = test_suite_path + "/valkyrie-tests.sh"
        valkyrie_binary_path = None
    utilities.execute_command(copy_command)
    patch_dir = dir_output_local + "/patches"
    if not os.path.isdir(patch_dir):
        os.makedirs(patch_dir)
    dir_process = dir_output_local + "/patches-processing"
    utilities.execute_command("mkdir {}".format(dir_process))
    return patch_dir, dir_process, valkyrie_binary_path, valkyrie_oracle_path


def repair_all(
    dir_info_list,
    experiment_info,
    tool_list,
    config_info,
    container_id_list,
    benchmark_name,
):
    consume_thread = None
    tool_thread_list = []
    parallel.initialize()
    time_duration = float(config_info[definitions.KEY_CONFIG_TIMEOUT])
    test_timeout = int(experiment_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE])
    total_timeout = time.time() + 60 * 60 * time_duration
    for index in range(0, len(tool_list)):
        dir_info = dir_info_list[index]
        repair_tool = tool_list[index]
        container_id = container_id_list[index]
        passing_id_list_str = experiment_info[definitions.KEY_PASSING_TEST]
        passing_test_list = []
        test_ratio = float(config_info[definitions.KEY_CONFIG_TEST_RATIO])
        if str(passing_id_list_str).replace(",", "").isnumeric():
            passing_test_list = passing_id_list_str.split(",")
        failing_test_list = str(experiment_info[definitions.KEY_FAILING_TEST]).split(
            ","
        )

        if index == 0:
            is_rank = len(tool_list) > 1
            validation_test_list = (
                    failing_test_list
                    + passing_test_list[: int(len(passing_test_list) * test_ratio)]
            )
            fix_source_file = str(experiment_info[definitions.KEY_FIX_FILE])

            if values.use_valkyrie:
                valkyrie_setup_info = setup_for_valkyrie(
                    dir_info, container_id, experiment_info, benchmark_name
                )
                patch_dir, dir_process, binary_path, oracle_path = valkyrie_setup_info
                v_path_info = (binary_path, oracle_path, fix_source_file)
                v_dir_info = (patch_dir, dir_process)
                v_config_info = (
                    validation_test_list,
                    is_rank,
                    total_timeout,
                    test_timeout,
                )
                consume_thread = threading.Thread(
                    target=parallel.consume_patches,
                    args=(v_path_info, v_dir_info, v_config_info),
                )
                consume_thread.start()

        if values.use_valkyrie:
            values.running_tool = True
        t_thread = threading.Thread(
            target=repair,
            args=(
                dir_info,
                experiment_info,
                repair_tool,
                config_info,
                container_id,
                benchmark_name,
            ),
        )
        t_thread.start()
        tool_thread_list.append((t_thread, repair_tool))

    for thread, tool in tool_thread_list:
        wait_time = 5
        if time.time() <= total_timeout:
            wait_time = total_timeout - time.time()
        thread.join(wait_time)
        if thread.is_alive():
            emitter.highlight(
                "\t\t\t[info] {}: thread is not done, setting event to kill thread.".format(
                    tool.name
                )
            )
            event = threading.Event()
            event.set()
            # The thread can still be running at this point. For example, if the
            # thread's call to isSet() returns right before this call to set(), then
            # the thread will still perform the full 1 second sleep and the rest of
            # the loop before finally stopping.
        else:
            emitter.highlight(
                "\t\t\t[info] {}: thread has already finished.".format(tool.name)
            )

        # Thread can still be alive at this point. Do another join without a timeout
        # to verify thread shutdown.
        thread.join()
        # if tool.log_output_path:
        #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + tool.log_output_path
        #     utilities.execute_command(timestamp_command)

    values.running_tool = False
    if values.use_valkyrie:
        emitter.normal("\t\t\twaiting for validation pool")
        parallel.wait_validation()
        emitter.normal("\t\t\twaiting for consumer pool")
        consume_thread.join()
    # for t in tool_list:
    #     timestamp_command = "echo $(date -u '+%a %d %b %Y %H:%M:%S %p') >> " + t.log_output_path
    #     utilities.execute_command(timestamp_command)


def analyse_result(dir_info_list, experiment_info, tool_list):
    emitter.normal("\t\t[framework] analysing experiment results")
    bug_id = str(experiment_info[definitions.KEY_BUG_ID])
    failing_test_list = experiment_info[definitions.KEY_FAILING_TEST]
    first_start = None
    patch_dir = None
    index = -1
    for tool in tool_list:
        index = index + 1
        dir_info = dir_info_list[index]
        space_info, time_info, error_info = tool.analyse_output(
            dir_info, bug_id, failing_test_list
        )
        conf_id = str(values.config_id)
        exp_id = conf_id + "-" + bug_id
        values.analysis_results[exp_id] = [space_info, time_info]
        tool.print_analysis(space_info, time_info)
        tool.log_output_path = None
        logger.analysis(exp_id)
        dir_output = dir_info["local"]["artifacts"]
        patch_dir = dir_output + "/patches"
        if values.use_valkyrie:
            valkyrie.analyse_output(patch_dir, time_info)
            break


def retrieve_results(archive_name, tool: AbstractTool):
    emitter.normal("\t\tretrieving results for analysis")
    archive_path = (
        values.dir_main + "/results/" + tool.name.lower() + "/" + archive_name
    )
    if os.path.isfile(archive_path):
        extract_command = "cp " + archive_path + " " + values.dir_results + ";"
        extract_command += "cd " + values.dir_results + ";"
        extract_command += "tar -xf " + archive_name
        utilities.execute_command(extract_command)
        return True
    else:
        emitter.error("\t\t[error] result archive not found at " + archive_path)
        return False


def save_artifacts(dir_info_list, experiment_info, tool_list, container_id_list):
    emitter.normal("\t\t[framework] saving artifacts and cleaning up")
    index = -1
    for tool in tool_list:
        index = index + 1
        dir_info = dir_info_list[index]["local"]
        container_id = container_id_list[index]
        dir_expr = dir_info["experiment"]
        dir_artifacts = dir_info["artifacts"]
        dir_results = dir_info["results"]
        if not os.path.isdir(dir_results):
            os.system("mkdir -p {}".format(dir_results))
        tool.save_artefacts(dir_info)
        tool.post_process()
        save_command = "cp -f " + values.file_main_log + " " + dir_results + ";"
        save_command += "cp -f " + values.file_error_log + "/* " + dir_results
        utilities.execute_command(save_command)


def create_running_container(bug_image_id, repair_tool, dir_info, container_name):
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
    if not container.is_image_exist(container_name.lower()) or values.rebuild_base:
        tmp_dockerfile = "{}/Dockerfile-{}-{}".format(dir_info["local"]["setup"],
                                                       repair_tool.name, bug_image_id)
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
        container_name, dict(), container_name.lower()
    )
    copy_log_cmd = "docker cp {}:{} {}".format(
        tmp_container_id, dir_info["container"]["logs"], dir_info["local"]["logs"]
    )
    utilities.execute_command(copy_log_cmd)
    container.stop_container(tmp_container_id)
    container.remove_container(tmp_container_id)
    container_id = container.build_container(
        container_name, volume_list, container_name.lower()
    )
    return container_id


def run(benchmark, tool_list, bug_info, config_info):
    dir_info_list = []
    container_id_list = []
    index = 0
    bug_index = bug_info[definitions.KEY_ID]
    bug_name = str(bug_info[definitions.KEY_BUG_ID])
    config_id = config_info[definitions.KEY_ID]
    if definitions.KEY_CONFIG_TIMEOUT_TESTCASE in bug_info:
        config_info[definitions.KEY_CONFIG_TIMEOUT_TESTCASE] = bug_info[
            definitions.KEY_CONFIG_TIMEOUT_TESTCASE
        ]
    subject_name = str(bug_info[definitions.KEY_SUBJECT])
    dir_info = generate_dir_info(
        benchmark.name,
        subject_name,
        bug_name,
        "-".join(
            list(map(lambda x: x.name, tool_list))
            + [benchmark.name, subject_name, bug_name, "last"]
        ),
    )
    emitter.highlight("\t[profile] identifier: " + str(config_info[definitions.KEY_ID]))
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
    emitter.highlight("\t[meta-data] project: " + subject_name)
    emitter.highlight("\t[meta-data] bug ID: " + bug_name)
    emitter.highlight("\t[meta-data] logs directory: " + dir_info["local"]["logs"])
    emitter.highlight(
        "\t[meta-data] output directory: " + dir_info["local"]["artifacts"]
    )
    exp_img_id = None

    benchmark.update_dir_info(dir_info)
    if values.use_container:
        exp_img_id = benchmark.get_exp_image(bug_index, values.only_test)
    else:
        if not values.use_valkyrie:
            benchmark.setup_experiment(bug_index, None, values.only_test)

    for repair_tool in tool_list:
        index = index + 1
        container_id = None
        tool_name = repair_tool.name
        if len(tool_list) > 1:
            tool_name = "multi"
        dir_info = update_dir_info(dir_info, tool_name)
        dir_instr_local = dir_info["local"]["instrumentation"]
        dir_result_local = dir_info["local"]["results"]
        # emitter.information("directory is {}".format(dir_instr_local))
        if not os.path.isdir(dir_instr_local):
            emitter.warning(
                "\t\t[warning] there is no instrumentation for " + repair_tool.name
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
        if index == 1:
            dir_output_local = dir_info["local"]["artifacts"]
            dir_logs_local = dir_info["local"]["logs"]
            utilities.clean_artifacts(dir_output_local)
            utilities.clean_artifacts(dir_logs_local)
        benchmark.update_dir_info(dir_info)
        if values.use_container:
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
                exp_img_id, repair_tool, dir_info, container_name
            )
        container_id_list.append(container_id)
        dir_info_list.append(dir_info)

    if not values.only_setup:
        repair_all(
            dir_info_list,
            bug_info,
            tool_list,
            config_info,
            container_id_list,
            benchmark.name,
        )
        if not values.only_instrument:
            analyse_result(dir_info_list, bug_info, tool_list)
            save_artifacts(dir_info_list, bug_info, tool_list, container_id_list)
            tool_name = tool_list[0].name
            if len(tool_list) > 1:
                tool_name = "multi"
            dir_archive = join(values.dir_results , tool_name)
            dir_result = dir_info_list[0]["local"]["results"]
            archive_results(dir_result, dir_archive)
            utilities.clean_artifacts(dir_result)
