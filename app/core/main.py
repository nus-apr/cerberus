import getpass
import multiprocessing
import os
import signal
import sys
import time
import traceback
from argparse import Namespace
from multiprocessing import set_start_method
from typing import Any
from typing import cast
from typing import Dict
from typing import NoReturn
from typing import Optional

import rich.traceback
from rich import get_console

from app.core import configuration
from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import utilities
from app.core import values
from app.core.args import parse_args
from app.core.configs.Config import Config
from app.core.configs.ConfigDataFactory import ConfigDataFactory
from app.core.configs.ConfigDataLoader import ConfigDataLoader
from app.core.configs.ConfigValidationSchemas import config_validation_schema
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.configuration import Configurations
from app.core.identifiers import create_bug_image_identifier
from app.core.identifiers import create_task_identifier
from app.core.identifiers import create_task_image_identifier
from app.core.task import task
from app.core.task.dir_info import generate_dir_info
from app.core.task.image import prepare_experiment_image
from app.core.task.image import prepare_experiment_tool
from app.core.task.TaskProcessor import TaskProcessor
from app.core.task.typing.TaskList import TaskList
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.notification import notification
from app.ui import ui


def timeout_handler(signum: int, frame: Any) -> NoReturn:
    emitter.error("TIMEOUT Exception")
    raise Exception("end of time")


def shutdown(signum: int, frame: Any) -> NoReturn:
    # global stop_event
    emitter.warning("Exiting due to Terminate Signal")
    # stop_event.set()
    raise SystemExit


def bootstrap(arg_list: Namespace) -> Configurations:
    emitter.sub_title("Bootstrapping framework")
    config = Configurations()
    config.read_email_config_file()
    config.read_slack_config_file()
    config.read_discord_config_file()
    config.read_openai_config_file()
    config.read_anthropic_config_file()
    config.read_arg_list(arg_list)
    values.arg_pass = True
    config.update_configuration()
    config.print_configuration()
    return config


iteration = 0


def process_configs(
    task_config: TaskConfig,
    benchmark: AbstractBenchmark,
    experiment_item: Dict[str, Any],
    task_profile: Dict[str, Any],
    container_profile: Dict[str, Any],
) -> None:
    for k, v in task_config.__dict__.items():
        if k != "task_type" and v is not None:
            emitter.configuration(k, v)
            setattr(values, k, v)
    values.task_type.set(cast(TaskType, task_config.task_type))
    values.current_container_profile_id.set(container_profile[definitions.KEY_ID])
    values.current_task_profile_id.set(task_profile[definitions.KEY_ID])

    values.job_identifier.set(create_bug_image_identifier(benchmark, experiment_item))


def main() -> None:
    global iteration
    if not sys.warnoptions:
        import warnings

        warnings.simplefilter("ignore")

    rich.traceback.install(show_locals=True)
    parsed_args = parse_args()
    has_error = False
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.signal(signal.SIGTERM, shutdown)
    set_start_method("fork")
    start_time = time.time()
    utilities.create_output_directories()
    values.gpus = utilities.get_gpu_count()
    logger.create_log_files()

    return_code, (output, _) = utilities.run_command(
        f"groups {getpass.getuser()} | grep {definitions.GROUP_NAME}"
    )
    if return_code != 0 or not output or output.decode() == "":
        utilities.error_exit(
            f"User {getpass.getuser()} is not part of {definitions.GROUP_NAME} group or group does not exist. Please this is setup correctly"
        )

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
            iteration, has_error = ui.setup_ui(tasks)
        else:
            emitter.information("\t\t[framework] starting processing of tasks")
            has_error = process_tasks(tasks)

    except (SystemExit, KeyboardInterrupt) as e:
        pass
    except Exception as e:
        has_error = True
        values.ui_active = False
        emitter.error("Runtime Error")
        emitter.error(str(e))
        logger.error(traceback.format_exc())
    finally:
        container.clean_containers()
        get_console().show_cursor(True)
        # Final running time and exit message
        # os.system("ps -aux | grep 'python' | awk '{print $2}' | xargs kill -9")
        total_duration = format((time.time() - start_time) / 60, ".3f")
        if not parsed_args.parallel:
            notification.end(total_duration, has_error)
        emitter.end(total_duration, iteration, has_error)


def process_config_file(parsed_args: Namespace) -> Config:
    values.arg_pass = True
    config_loader = ConfigDataLoader(
        file_path=parsed_args.config_file,
        validation_schema=config_validation_schema,
    )
    config_loader.load()
    config_loader.validate()
    config = ConfigDataFactory.create(config_data_dict=config_loader.get_config_data())
    configuration.process_overrides(
        parsed_args, config
    )  # Allow for overriding of the config by the command line
    values.debug = config.general.debug_mode
    values.secure_hash = config.general.secure_hash
    values.use_parallel = config.general.parallel_mode
    values.cpus = min(multiprocessing.cpu_count() - 2, config.general.cpus)
    values.gpus = min(utilities.get_gpu_count(), config.general.gpus)
    return config


def process_tasks(tasks: TaskList) -> bool:
    has_error = False
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
        tool.tool_tag = tool_tag
        bug_name = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        # Allow for a special base setup folder if needed
        dir_setup_extended = (
            os.path.join(
                values.dir_benchmark,
                benchmark.name,
                subject_name,
                f"{bug_name}-{tool_tag}",
                "",
            )
            if tool_tag
            else None
        )
        dir_info = generate_dir_info(
            benchmark.name,
            subject_name,
            bug_name,
            dir_setup_extended,
        )

        experiment_image_id = prepare_experiment_image(
            benchmark,
            experiment_item,
            cpus,
            [],
            tool_tag,
            locally_running=tool.locally_running,
        )

        if task_config.task_type == "prepare":
            iteration = iteration + 1
            emitter.sub_sub_title(
                "Experiment #{} - Bug #{} Run #{}".format(iteration, bug_index, 1)
            )
            continue

        image_name = create_task_image_identifier(
            benchmark,
            tool,
            experiment_item,
            tool_tag,
        )
        prepare_experiment_tool(
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

            (err, _) = task.run(
                benchmark,
                tool,
                experiment_item,
                task_profile,
                container_profile,
                key,
                cpus,
                gpus,
                str(run_index),
                image_name,
                dir_setup_extended=dir_setup_extended,
            )
            if err:
                has_error = True
    return has_error
