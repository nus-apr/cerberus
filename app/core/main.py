import os
import signal
import sys
import time
import traceback
from argparse import Namespace
from multiprocessing import set_start_method
from typing import Any
from typing import Dict
from typing import List

import rich.traceback
from rich import get_console

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import utilities
from app.core import values
from app.core.args import parse_args
from app.core.configs.ConfigDataFactory import ConfigDataFactory
from app.core.configs.ConfigDataLoader import ConfigDataLoader
from app.core.configs.ConfigValidationSchemas import config_validation_schema
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.configuration import Configurations
from app.core.task import task
from app.core.task.TaskProcessor import TaskProcessor
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.notification import notification
from app.ui import ui


def create_output_directories():
    dir_list = [
        values.dir_logs,
        values.dir_output_base,
        values.dir_log_base,
        values.dir_artifacts,
        values.dir_results,
        values.dir_experiments,
        values.dir_summaries,
    ]

    for dir_i in dir_list:
        if not os.path.isdir(dir_i):
            os.makedirs(dir_i)


def timeout_handler(signum, frame):
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def shutdown(signum, frame):
    # global stop_event
    emitter.warning("Exiting due to Terminate Signal")
    # stop_event.set()
    raise SystemExit


def bootstrap(arg_list: Namespace):
    emitter.sub_title("Bootstrapping framework")
    config = Configurations()
    config.read_email_config_file()
    config.read_slack_config_file()
    config.read_discord_config_file()
    config.read_arg_list(arg_list)
    values.arg_pass = True
    config.update_configuration()
    config.print_configuration()


iteration = 0


def run(
    tool_list: List[AbstractTool],
    benchmark: AbstractBenchmark,
    task_profiles: Dict[str, Dict[str, Any]],
    container_profiles: Dict[str, Dict[str, Any]],
):
    global iteration
    emitter.sub_title(f"Running {values.task_type.get()} task")

    for task_profile in map(
        lambda task_profile_id: task_profiles[task_profile_id],
        values.task_profile_id_list,
    ):
        task_profile[definitions.KEY_TOOL_PARAMS] = values.tool_params
        task_profile[definitions.KEY_TOOL_TAG] = values.tool_tag
        for container_profile in map(
            lambda container_profile_id: container_profiles[container_profile_id],
            values.container_profile_id_list,
        ):

            values.current_task_profile_id.set(task_profile[definitions.KEY_ID])
            values.current_container_profile_id.set(
                container_profile[definitions.KEY_ID]
            )
            for experiment_item in filter_experiment_list(benchmark):
                bug_index = experiment_item[definitions.KEY_ID]
                cpu = ",".join(
                    map(
                        str,
                        range(
                            container_profile.get(
                                definitions.KEY_CONTAINER_CPU_COUNT, values.cpus
                            )
                        ),
                    )
                )
                bug_name = str(experiment_item[definitions.KEY_BUG_ID])
                subject_name = str(experiment_item[definitions.KEY_SUBJECT])
                if values.use_container:
                    values.job_identifier.set(
                        "-".join([benchmark.name, subject_name, bug_name])
                    )
                dir_info = task.generate_dir_info(
                    benchmark.name, subject_name, bug_name
                )
                benchmark.update_dir_info(dir_info)
                experiment_image_id = None
                if values.only_setup:
                    iteration = iteration + 1
                    emitter.sub_sub_title(
                        "Experiment #{} - Bug #{}".format(iteration, bug_index)
                    )
                    task.prepare_experiment(benchmark, experiment_item, cpu)
                    continue

                for tool in tool_list:
                    image_args = [tool.name, benchmark.name, subject_name, bug_name]

                    if task_profile[definitions.KEY_TOOL_TAG] != "":
                        image_args.append(task_profile[definitions.KEY_TOOL_TAG])

                    image_name = "-".join(image_args)

                    experiment_image_id = task.prepare_experiment(
                        benchmark, experiment_item, cpu
                    )
                    task.prepare_experiment_tool(
                        experiment_image_id,
                        tool,
                        dir_info,
                        image_name,
                        task_profile[definitions.KEY_TOOL_TAG],
                    )

                    for run_index in range(values.runs):
                        iteration = iteration + 1
                        emitter.sub_sub_title(
                            "Experiment #{} - Bug #{} Run #{}".format(
                                iteration, bug_index, run_index + 1
                            )
                        )
                        tool_tag = task_profile[definitions.KEY_TOOL_TAG]
                        key = "-".join(
                            [
                                benchmark.name,
                                tool.name
                                if tool_tag == ""
                                else f"{tool.name}-{tool_tag}",
                                experiment_item[definitions.KEY_SUBJECT],
                                experiment_item[definitions.KEY_BUG_ID],
                                task_profile[definitions.KEY_ID],
                                container_profile[definitions.KEY_ID],
                                str(run_index),
                            ]
                        )

                        task.run(
                            benchmark,
                            tool,
                            experiment_item,
                            task_profile,
                            container_profile,
                            key,
                            cpu,
                            experiment_image_id,
                        )


def get_task_profiles() -> Dict[str, Dict[str, Any]]:
    emitter.normal("\t[framework] loading repair profile setup")
    task_profiles = configuration.load_profiles(values.file_task_profiles)
    for task_profile_id in values.task_profile_id_list:
        if task_profile_id not in task_profiles:
            utilities.error_exit("invalid task profile id {}".format(task_profile_id))
    return task_profiles


def get_container_profiles() -> Dict[str, Dict[str, Any]]:
    emitter.normal("\t[framework] loading container profile setup")
    container_profiles = configuration.load_profiles(values.file_container_profiles)
    for container_profile_id in values.container_profile_id_list:
        if container_profile_id not in container_profiles:
            utilities.error_exit(
                "invalid container profile id {}".format(container_profile_id)
            )
    return container_profiles


def get_tools() -> List[AbstractTool]:
    tool_list: List[AbstractTool] = []
    if values.task_type.get() == "prepare":
        return tool_list
    for tool_name in values.tool_list:
        tool = configuration.load_tool(tool_name, values.task_type.get(None) or "boom")
        if not values.only_analyse:
            tool.check_tool_exists()
        tool_list.append(tool)
    emitter.highlight(
        f"\t[framework] {values.task_type.get()}-tool(s): "
        + " ".join([x.name for x in tool_list])
    )
    return tool_list


def get_benchmark() -> AbstractBenchmark:
    benchmark = configuration.load_benchmark(values.benchmark_name.lower())
    emitter.highlight(
        f"\t[framework] {values.task_type.get()}-benchmark: {benchmark.name}"
    )
    return benchmark


def filter_experiment_list(benchmark: AbstractBenchmark):
    filtered_list = []
    experiment_list = benchmark.get_list()
    for bug_index in range(1, benchmark.size + 1):
        experiment_item = experiment_list[bug_index - 1]
        subject_name = experiment_item[definitions.KEY_SUBJECT]
        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        if values.bug_id_list and bug_name not in values.bug_id_list:
            continue
        if values.bug_index_list and bug_index not in values.bug_index_list:
            continue
        if values.skip_index_list and str(bug_index) in values.skip_index_list:
            continue
        if values.start_index and bug_index < values.start_index:
            continue
        if values.subject_name and values.subject_name != subject_name:
            continue
        if values.end_index and bug_index > values.end_index:
            break
        filtered_list.append(experiment_item)
    return filtered_list


def process_configs(
    task_config: TaskConfig,
    benchmark: AbstractBenchmark,
    experiment_item,
    task_profile: Dict[str, Any],
    container_profile: Dict[str, Any],
):
    for (k, v) in task_config.__dict__.items():
        if k != "task_type" and v is not None:
            emitter.configuration(k, v)
            setattr(values, k, v)
    values.task_type.set(task_config.task_type)
    values.current_container_profile_id.set(container_profile[definitions.KEY_ID])
    values.current_task_profile_id.set(task_profile[definitions.KEY_ID])

    if values.use_container:
        values.job_identifier.set(
            "-".join(
                [
                    benchmark.name,
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                ]
            )
        )


def main():
    global iteration
    if not sys.warnoptions:
        import warnings

        warnings.simplefilter("ignore")

    rich.traceback.install(show_locals=True)
    parsed_args = parse_args()
    is_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    set_start_method("spawn")
    start_time = time.time()
    create_output_directories()
    logger.create_log_files()
    # TODO Do overwrite magic
    bootstrap(parsed_args)
    try:
        emitter.title(
            "Starting {} (Program Repair Framework) ".format(values.tool_name)
        )

        if parsed_args.config_file:
            values.arg_pass = True
            config_loader = ConfigDataLoader(
                file_path=parsed_args.config_file,
                validation_schema=config_validation_schema,
            )
            config_loader.load()
            config_loader.validate()
            config = ConfigDataFactory.create(
                config_data_dict=config_loader.get_config_data()
            )
            tasks = TaskProcessor.execute(config)
            values.debug = config.general.debug_mode
            values.secure_hash = config.general.secure_hash
            if config.general.parallel_mode:
                info = sys.version_info
                if info.major < 3 or info.minor < 10:
                    utilities.error_exit(
                        "Parallel mode is currently supported only for versions 3.10+"
                    )
                iteration = ui.setup_ui(tasks)
            else:
                # The tool and benchmark images are going to be created while enumerating
                for iteration, (task_config, task_data) in enumerate(tasks):
                    (
                        benchmark,
                        tool,
                        experiment_item,
                        task_profile,
                        container_profile,
                        bug_index,
                    ) = task_data
                    process_configs(
                        task_config,
                        benchmark,
                        experiment_item,
                        task_profile,
                        container_profile,
                    )

                    cpu = ",".join(
                        map(
                            str,
                            range(
                                container_profile.get(
                                    definitions.KEY_CONTAINER_CPU_COUNT, values.cpus
                                )
                            ),
                        )
                    )
                    experiment_image_id = task.prepare_experiment(
                        benchmark, experiment_item, cpu
                    )
                    tool_tag = task_profile.get(definitions.KEY_TOOL_TAG, "")

                    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
                    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
                    dir_info = task.generate_dir_info(
                        benchmark.name, subject_name, bug_name
                    )

                    image_args = [tool.name, benchmark.name, subject_name, bug_name]

                    if task_profile[definitions.KEY_TOOL_TAG] != "":
                        image_args.append(task_profile[definitions.KEY_TOOL_TAG])

                    image_name = "-".join(image_args)
                    task.prepare_experiment_tool(
                        experiment_image_id,
                        tool,
                        dir_info,
                        image_name,
                        task_profile[definitions.KEY_TOOL_TAG],
                    )

                    for run_index in range(task_config.runs):
                        iteration = iteration + 1
                        emitter.sub_sub_title(
                            "Experiment #{} - Bug #{} Run #{}".format(
                                iteration, bug_index, run_index + 1
                            )
                        )

                        key = "-".join(
                            [
                                benchmark.name,
                                tool.name
                                if tool_tag == ""
                                else f"{tool.name}-{tool_tag}",
                                experiment_item[definitions.KEY_SUBJECT],
                                experiment_item[definitions.KEY_BUG_ID],
                                task_profile[definitions.KEY_ID],
                                container_profile[definitions.KEY_ID],
                                str(run_index),
                            ]
                        )

                        if not values.only_setup:
                            task.run(
                                benchmark,
                                tool,
                                experiment_item,
                                task_profile,
                                container_profile,
                                key,
                                cpu,
                                experiment_image_id,
                            )
        else:
            if not parsed_args.task_type:
                utilities.error_exit(
                    "Configuration file was not passed. Please provide a task type!"
                )
            if parsed_args.parallel:
                info = sys.version_info
                if info.major < 3 or info.minor < 10:
                    utilities.error_exit(
                        "Parallel mode is currently supported only for versions 3.10+"
                    )
                iteration = ui.setup_ui()
            else:
                run(
                    get_tools(),
                    get_benchmark(),
                    get_task_profiles(),
                    get_container_profiles(),
                )
    except (SystemExit, KeyboardInterrupt) as e:
        pass
    except Exception as e:
        is_error = True
        values.ui_active = False
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        get_console().show_cursor(True)
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, ".3f")
        if not parsed_args.parallel:
            notification.end(total_duration, is_error)
        emitter.end(total_duration, iteration, is_error)
