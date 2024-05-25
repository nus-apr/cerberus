import multiprocessing
import signal
import sys
import time
import traceback
from argparse import Namespace
from multiprocessing import set_start_method
from typing import Any
from typing import cast
from typing import Dict
from typing import Optional

import rich.traceback
from rich import get_console

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
from app.core.task.TaskProcessor import TaskList
from app.core.task.TaskProcessor import TaskProcessor
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.notification import notification
from app.ui import ui


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
    return config


def create_task_image_identifier(
    benchmark: AbstractBenchmark,
    tool: AbstractTool,
    experiment_item: Dict[str, Any],
    tag: Optional[str] = None,
):
    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
    image_args = [tool.name, benchmark.name, subject_name, bug_name]

    if tag and tag != "":
        image_args.append(tag)

    image_name = "-".join(map(lambda x: x.replace("-", "_"), image_args))
    return image_name.lower().replace(".", "_")


def create_bug_image_identifier(
    benchmark: AbstractBenchmark, experiment_item: Dict[str, Any]
):
    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
    return (
        "-".join(
            map(lambda x: x.replace("-", "_"), [benchmark.name, subject_name, bug_name])
        )
        .lower()
        .replace(".", "_")
    )


def create_task_identifier(
    benchmark: AbstractBenchmark,
    task_profile,
    container_profile,
    experiment_item,
    tool: AbstractTool,
    run_index: str,
    tool_tag: str,
):
    return "-".join(
        [
            benchmark.name,
            tool.name if tool_tag == "" else f"{tool.name}-{tool_tag}",
            experiment_item[definitions.KEY_SUBJECT],
            experiment_item[definitions.KEY_BUG_ID],
            task_profile[definitions.KEY_ID],
            container_profile[definitions.KEY_ID],
            run_index,
        ]
    ).replace(".", "_")


iteration = 0


def process_configs(
    task_config: TaskConfig,
    benchmark: AbstractBenchmark,
    experiment_item,
    task_profile: Dict[str, Any],
    container_profile: Dict[str, Any],
):
    for k, v in task_config.__dict__.items():
        if k != "task_type" and v is not None:
            emitter.configuration(k, v)
            setattr(values, k, v)
    values.task_type.set(cast(TaskType, task_config.task_type))
    values.current_container_profile_id.set(container_profile[definitions.KEY_ID])
    values.current_task_profile_id.set(task_profile[definitions.KEY_ID])

    if values.use_container:
        values.job_identifier.set(
            create_bug_image_identifier(benchmark, experiment_item)
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
    utilities.create_output_directories()
    values.gpus = utilities.get_gpu_count()
    logger.create_log_files()
    # TODO Do overwrite magic
    config_obj = bootstrap(parsed_args)
    try:
        emitter.title(
            "Starting {} (Program Repair Framework) ".format(values.tool_name)
        )

        tasks = None
        if parsed_args.config_file:
            config = process_config_file(parsed_args)
            tasks = TaskProcessor.execute(config)
            # The tool and benchmark images are going to be created while enumerating
        else:
            if not parsed_args.task_type:
                utilities.error_exit(
                    "Configuration file was not passed. Please provide a task type!"
                )
            tasks = config_obj.construct_task_list()

        if tasks is None:
            utilities.error_exit("Tasks were not assigned??")

        if values.use_parallel:
            info = sys.version_info
            if info.major < 3 or info.minor < 10:
                utilities.error_exit(
                    "Parallel mode is currently supported only for versions 3.10+"
                )
            iteration = ui.setup_ui(tasks)
        else:
            emitter.information("\t\t[framework] starting processing of tasks")
            process_tasks(tasks)

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


def process_config_file(parsed_args):
    values.arg_pass = True
    config_loader = ConfigDataLoader(
        file_path=parsed_args.config_file,
        validation_schema=config_validation_schema,
    )
    config_loader.load()
    config_loader.validate()
    config = ConfigDataFactory.create(config_data_dict=config_loader.get_config_data())
    values.debug = config.general.debug_mode
    values.secure_hash = config.general.secure_hash
    values.use_parallel = config.general.parallel_mode
    values.cpus = min(multiprocessing.cpu_count() - 2, config.general.cpus)
    values.gpus = min(utilities.get_gpu_count(), config.general.gpus)
    return config


def process_tasks(tasks: TaskList):
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

        cpus = list(
            map(
                str,
                range(
                    container_profile.get(
                        definitions.KEY_CONTAINER_CPU_COUNT, values.cpus
                    )
                ),
            )
        )

        gpus = list(
            map(
                str,
                range(
                    container_profile.get(
                        definitions.KEY_CONTAINER_GPU_COUNT, values.gpus
                    )
                ),
            )
        )

        tool_tag = task_profile.get(definitions.KEY_TOOL_TAG, "")

        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        dir_info = task.generate_dir_info(
            benchmark.name,
            subject_name,
            bug_name,
            tool_tag,
        )

        if task_config.task_type == "prepare":
            iteration = iteration + 1
            emitter.sub_sub_title(
                "Experiment #{} - Bug #{} Run #{}".format(iteration, bug_index, 1)
            )
            task.prepare_experiment(benchmark, experiment_item, cpus, [], tag=tool_tag)
            continue

        experiment_image_id = task.prepare_experiment(
            benchmark, experiment_item, cpus, [], tool_tag
        )

        image_name = create_task_image_identifier(
            benchmark,
            tool,
            experiment_item,
            tool_tag,
        )
        task.prepare_experiment_tool(
            experiment_image_id,
            tool,
            task_profile,
            dir_info,
            image_name,
            experiment_item,
            tool_tag,
        )
        for run_index in range(task_config.runs):
            iteration = iteration + 1
            emitter.sub_sub_title(
                "Experiment #{} - Bug #{} Run #{}".format(
                    iteration, bug_index, run_index + 1
                )
            )

            key = create_task_identifier(
                benchmark,
                task_profile,
                container_profile,
                experiment_item,
                tool,
                str(run_index),
                tool_tag,
            )

            task.run(
                benchmark,
                tool,
                experiment_item,
                task_profile,
                container_profile,
                key,
                cpus,
                gpus,
                image_name,
            )
