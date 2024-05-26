import asyncio
import queue
import threading
import time
import traceback
from asyncio import AbstractEventLoop
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from os.path import join
from random import randint
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional
from typing import Set
from typing import Tuple

from textual import on
from textual.app import App
from textual.app import ComposeResult
from textual.events import Key
from textual.reactive import Reactive
from textual.widget import Widget
from textual.widgets import DataTable
from textual.widgets import Footer
from textual.widgets import Header
from textual.widgets import RichLog
from textual.widgets import Static
from textual.widgets._data_table import ColumnKey

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import logger
from app.core import main
from app.core import utilities
from app.core import values
from app.core import writer
from app.core.configs.tasks_data.TaskConfig import TaskConfig
from app.core.task import task
from app.core.task.stats.RepairToolStats import RepairToolStats
from app.core.task.stats.ToolStats import ToolStats
from app.core.task.TaskProcessor import TaskList
from app.core.task.TaskStatus import TaskStatus
from app.core.task.typing.TaskType import TaskType
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.notification import notification
from app.ui.messages import JobAllocate
from app.ui.messages import JobFinish
from app.ui.messages import JobMount
from app.ui.messages import Write

all_subjects_id = "all_subjects"
finished_subjects_id = "finished_subjects"
error_subjects_id = "error_subjects"
running_subjects_id = "running_subjects"

log_map: Dict[str, RichLog] = {}
job_time_map: Dict[str, Tuple[int, int, int, AbstractTool]] = {}
job_time_map_mutex = threading.Lock()

job_condition = threading.Condition()

Result = Tuple[str, TaskStatus, Dict[str, str], ToolStats]


class Cerberus(App[List[Result]]):
    """The main window"""

    COLUMNS: Dict[str, Dict[str, ColumnKey]] = {
        "ID": {},
        "Benchmark": {},
        "Tool": {},
        "Subject": {},
        "Bug ID": {},
        "Run": {},
        "Tag": {},
        definitions.UI_TASK_PROFILE: {},
        definitions.UI_CONTAINER_PROFILE: {},
        definitions.UI_STARTED_AT: {},
        definitions.UI_SHOULD_FINISH: {},
        definitions.UI_STATUS: {},
        definitions.UI_PLAUSIBLE_PATCHES: {},
        definitions.UI_DURATION: {},
    }

    SUB_TITLE = "Program Repair Framework"

    BINDINGS = [
        ("d", "toggle_dark", "Toggle dark mode"),
        # ("a", "show_all_subjects", "Show All Subjects"),
        # ("r", "show_running_subjects", "Show Running Subjects"),
        # ("f", "show_finished_subjects", "Show Finished Subjects"),
        # ("e", "show_error_subjects", "Show Erred Subjects"),
    ]

    tasks: Optional[TaskList]

    async def _on_exit_app(self) -> None:
        values.ui_active = False
        self.jobs_cancelled = True
        self.completed_all = True

        # Allow all processes to wake up and process that they are cancelled
        self.free_cpus = 10000
        self.free_gpus = 10000

        with job_condition:
            job_condition.notify_all()
        for id, (task, tool) in self.jobs.items():
            if not task.done():
                if tool.container_id:
                    container.stop_container(tool.container_id)
                task.cancel()
                self.finished_subjects.append(
                    (id, TaskStatus.CANCELLED, {}, ToolStats())
                )
        self._return_value = self.finished_subjects
        return await super()._on_exit_app()

    def on_mount(self) -> None:
        self.completed_all = False
        self.selected_subject = None
        self.finished_subjects: List[Result] = []

        self.jobs_remaining_mutex = threading.Lock()
        self.jobs_remaining = 0
        self.jobs: Dict[str, Tuple[asyncio.Future, AbstractTool]] = {}

        self.jobs_cancelled = False

        self.setup_resource_allocation()

        values.ui_active = True

        self.setup_column_keys()

        loop = asyncio.get_running_loop()
        loop.set_default_executor(ThreadPoolExecutor(max_workers=values.cpus + 2))

        asyncio.get_running_loop().run_in_executor(
            None,
            self.watchdog,
        )

        asyncio.get_running_loop().run_in_executor(
            None,
            self.prepare_tasks_run,
            loop,
        )

    def watchdog(self) -> None:
        while not self.completed_all:
            now = int(time.time())
            to_del = []

            if job_time_map_mutex.acquire(timeout=4):
                for job_id, info in job_time_map.items():
                    (nonce, start, limit, tool) = info
                    if now - start > limit:
                        if not self.jobs[job_id][0].done():
                            # self.debug_print("TIME TO KILL {}".format(info))
                            # log_map[job_id].write("KILLED BY WATCHDOG")
                            # self.update_status(job_id, "KILLED BY WATCHDOG")
                            if tool.container_id:
                                # log_map["root"].write(
                                #    "Killing {}".format(tool.container_id)
                                # )
                                # Currently this kills the container and the tool gets a 137 status for the run command
                                # Possibly we can also track a "critical" section of the tool run
                                # as killing it outside of that specific moment does not seem sensible
                                container.kill_container(tool.container_id)
                            else:
                                pass
                                # emitter.information(
                                #    "Cannot kill a local process as I do not know the exact process id"
                                # )
                            # log_map[job_id].write("Cancelled")
                        to_del.append(job_id)

                for job_id in to_del:
                    del job_time_map[job_id]
                job_time_map_mutex.release()
            time.sleep(30)

    def setup_resource_allocation(self) -> None:
        self.free_cpus = values.cpus
        self.free_gpus = values.gpus

        self.gpu_queue: queue.Queue[str] = queue.Queue(values.gpus + 1)
        self.cpu_queue: queue.Queue[str] = queue.Queue(values.cpus + 1)
        for cpu in range(values.cpus):
            self.cpu_queue.put(str(cpu))
        for gpu in range(values.gpus):
            self.gpu_queue.put(str(gpu))

    def setup_column_keys(self) -> None:
        for table in self.query(DataTable):
            column_keys = table.add_columns(*Cerberus.COLUMNS.keys())
            if not table.id:
                utilities.error_exit(
                    "CustomDataTable does not have ID. This should not happen"
                )
            for column_name, column_key in zip(Cerberus.COLUMNS.keys(), column_keys):
                Cerberus.COLUMNS[column_name][table.id] = column_key

    def _on_idle(self) -> None:
        try:
            super()._on_idle()
        except Exception as e:
            self.debug_print("The inner idle handler failed...")
            self.debug_print(e)
            pass
        # self.debug_print("Idle")

    def prepare_tasks_run(self, loop: AbstractEventLoop):
        try:
            self.hide(self.query_one("#" + all_subjects_id))

            self.is_preparing = True

            self.show(log_map["root"])
            self.query_one(Static).update(
                "Cerberus is preparing tool and benchmark images"
            )
            tasks = []
            if self.tasks:
                tasks = list(
                    self.tasks
                )  # Sequentially prepares the benchmarks and tools, will be parallelized later on

            if values.use_container:
                self.prepare_subjects(loop, tasks)
                if not values.only_setup:
                    self.prepare_tool_subjects(loop, tasks)

            if values.only_setup:
                self.exit(self.finished_subjects)

            self.hide(self.query_one(Static))
            if not values.debug:
                self.hide(log_map["root"])
            self.is_preparing = False

            self.show(self.query_one("#" + all_subjects_id))
            total_jobs = 0
            for iteration, (
                task_config,
                (
                    benchmark,
                    tool,
                    experiment_item,
                    task_profile,
                    container_profile,
                    bug_index,
                ),
            ) in enumerate(tasks):
                image_name = main.create_task_image_identifier(
                    benchmark,
                    tool,
                    experiment_item,
                    task_profile.get(definitions.KEY_TOOL_TAG, None),
                )
                runs = task_config.runs
                if task_config.task_type == "prepare":
                    runs = 1

                for run in range(runs):
                    total_jobs += 1
                    self.construct_job(
                        benchmark,
                        tool,
                        task_profile,
                        container_profile,
                        experiment_item,
                        image_name,
                        iteration,
                        str(run),
                        task_config,
                    )
            self.jobs_remaining_mutex.acquire(blocking=True)
            self.jobs_remaining += total_jobs
            self.jobs_remaining_mutex.release()

        except Exception as e:
            self.show(self.query_one(Static))
            self.query_one(Static).update(
                "{}\n{}".format(str(e), traceback.format_exc())
            )
            self.debug_print("I got exception {}".format(e))

    def prepare_subjects(
        self,
        loop: AbstractEventLoop,
        tasks: List[
            Tuple[
                TaskConfig,
                Tuple[
                    AbstractBenchmark,
                    AbstractTool,
                    Any,
                    Dict[str, Any],
                    Dict[str, Any],
                    str,
                ],
            ]
        ],
    ):
        self.query_one(Static).update("Cerberus is preparing the subject images.")
        complete_images: queue.Queue[Tuple[str, str, bool]] = queue.Queue(0)

        # The Logic here is currently differernt as one generally just needs a single CPU to build a project
        def prepare_subjects_job(
            benchmark: AbstractBenchmark, experiment_item, job_identifier: str, tag: str
        ):
            cpu = self.cpu_queue.get(block=True, timeout=None)
            bug_name = str(experiment_item[definitions.KEY_BUG_ID])
            subject_name = str(experiment_item[definitions.KEY_SUBJECT])
            values.job_identifier.set(job_identifier)
            emitter.information(
                "\t[framework] Starting image check for bug {} from subject {}".format(
                    bug_name, subject_name
                )
            )
            dir_info = task.generate_dir_info(
                benchmark.name, subject_name, bug_name, tag
            )
            benchmark.update_dir_info(dir_info)
            try:
                emitter.information(
                    "\t[framework] Image check for bug {} from subject {}".format(
                        bug_name, subject_name
                    )
                )
                task.prepare_experiment(
                    benchmark, experiment_item, [str(cpu)], [], tag
                )  # Assuming no GPU is used for preparation
                complete_images.put(
                    (
                        experiment_item[definitions.KEY_ID],
                        job_identifier,
                        True,
                    )
                )
            except Exception as e:
                emitter.information(
                    "\t[framework] Error {} for bug {} from subject {}".format(
                        e, bug_name, subject_name
                    )
                )
                complete_images.put(
                    (
                        experiment_item[definitions.KEY_ID],
                        job_identifier,
                        False,
                    )
                )
            finally:
                self.cpu_queue.put(cpu, block=False)
            emitter.information(
                "\t[framework] Finished image check for bug {} from subject {}".format(
                    bug_name, subject_name
                )
            )

        image_list: Set[str] = set()
        for (
            task_config,
            (
                benchmark,
                tool,
                experiment_item,
                task_profile,
                container_profile,
                bug_index,
            ),
        ) in tasks:
            job_identifier = main.create_bug_image_identifier(
                benchmark, experiment_item
            )
            if job_identifier in image_list:
                continue

            main.process_configs(
                task_config, benchmark, experiment_item, task_profile, container_profile
            )

            image_list.add(job_identifier)
            loop.run_in_executor(
                None,
                prepare_subjects_job,
                benchmark,
                experiment_item,
                job_identifier,
                task_profile.get(definitions.KEY_TOOL_TAG, ""),
            )
        while complete_images.qsize() != len(image_list):
            self.query_one(Static).update(
                "Cerberus is preparing the subject images ({} out of {} complete).".format(
                    complete_images.qsize(), len(image_list)
                )
            )
            pass
        while complete_images.qsize() != 0:
            (id, job_identifier, success) = complete_images.get()
            if not success:
                emitter.warning(
                    "\t[warning] Failed building image {} for job {}".format(
                        id, job_identifier
                    )
                )

    def prepare_tool_subjects(
        self,
        loop: AbstractEventLoop,
        tasks: List[
            Tuple[
                TaskConfig,
                Tuple[
                    AbstractBenchmark,
                    AbstractTool,
                    Any,
                    Dict[str, Any],
                    Dict[str, Any],
                    str,
                ],
            ]
        ],
    ):
        self.query_one(Static).update(
            "Cerberus is preparing the specialised subject images."
        )
        complete_images: queue.Queue[
            Tuple[str, str, Optional[str], bool]
        ] = queue.Queue(0)

        # The Logic here is currently differernt as one generally just needs a single CPU to build a project
        def prepare_tool_subjects_job(
            benchmark: AbstractBenchmark,
            tool: AbstractTool,
            experiment_item,
            task_profile: Dict[str, Any],
            job_identifier: str,
        ):
            cpu = self.cpu_queue.get(block=True, timeout=None)
            bug_name = str(experiment_item[definitions.KEY_BUG_ID])
            subject_name = str(experiment_item[definitions.KEY_SUBJECT])
            values.job_identifier.set(job_identifier)
            emitter.information(
                "\t[framework] Starting image check for bug {} from subject {}".format(
                    bug_name, subject_name
                )
            )
            dir_info = task.generate_dir_info(
                benchmark.name,
                subject_name,
                bug_name,
                task_profile.get(definitions.KEY_TOOL_TAG, ""),
            )
            benchmark.update_dir_info(dir_info)
            try:
                emitter.information(
                    "\t[framework] Image check for bug {} from subject {}".format(
                        bug_name, subject_name
                    )
                )
                # Ignore the rebuild as previously all bugs were prepared
                # Assuming that no GPUs are needed for preparation
                experiment_image_id = task.prepare_experiment(
                    benchmark,
                    experiment_item,
                    [str(cpu)],
                    [],
                    task_profile.get(definitions.KEY_TOOL_TAG, ""),
                    ignore_rebuild=True,
                )

                emitter.information(
                    "\t[framework] Image check for bug {} from subject {} for tool {}".format(
                        bug_name, subject_name, tool.name
                    )
                )

                tool_experiment_image_id = task.prepare_experiment_tool(
                    experiment_image_id,
                    tool,
                    task_profile,
                    dir_info,
                    job_identifier,
                    experiment_item,
                    task_profile[definitions.KEY_TOOL_TAG],
                )
                complete_images.put(
                    (
                        experiment_item[definitions.KEY_ID],
                        job_identifier,
                        tool_experiment_image_id,
                        True,
                    )
                )
            except Exception as e:
                emitter.information(
                    "\t[framework] Error {} for bug {} from subject {} for tool {}".format(
                        e, bug_name, subject_name, tool.name
                    )
                )
                complete_images.put(
                    (
                        experiment_item[definitions.KEY_ID],
                        job_identifier,
                        None,
                        False,
                    )
                )
            finally:
                self.cpu_queue.put(cpu, block=False)
            emitter.information(
                "\t[framework] Finished image check for {} {}".format(
                    bug_name, subject_name
                )
            )

        image_list: Set[str] = set()
        for (
            task_config,
            (
                benchmark,
                tool,
                experiment_item,
                task_profile,
                container_profile,
                bug_index,
            ),
        ) in tasks:
            image_name = main.create_task_image_identifier(
                benchmark,
                tool,
                experiment_item,
                task_profile.get(definitions.KEY_TOOL_TAG, None),
            )

            if image_name in image_list:
                continue

            main.process_configs(
                task_config, benchmark, experiment_item, task_profile, container_profile
            )
            image_list.add(image_name)
            loop.run_in_executor(
                None,
                prepare_tool_subjects_job,
                benchmark,
                tool,
                experiment_item,
                task_profile,
                image_name,
            )
        while complete_images.qsize() != len(image_list):
            self.query_one(Static).update(
                "Cerberus is preparing the specialised subject images ({} out of {} complete).".format(
                    complete_images.qsize(), len(image_list)
                )
            )
            pass
        while complete_images.qsize() != 0:
            (id, job_identifier, image_name, success) = complete_images.get()
            if not success:
                emitter.warning(
                    "\t[warning] Failed building image {}".format(image_name)
                )

    def change_table(self, new_id: str):
        return
        if self.is_preparing:
            return
        self.debug_print("Changing table!")
        try:
            self.selected_table: DataTable

            self.hide(self.selected_table)

            self.selected_table = self.query_one(new_id, DataTable)

            self.show(self.selected_table)
        except Exception as e:
            self.debug_print(e)

    def action_show_finished_subjects(self):
        self.change_table("#" + finished_subjects_id)

    def action_show_running_subjects(self):
        self.change_table("#" + running_subjects_id)

    def action_show_all_subjects(self):
        self.change_table("#" + all_subjects_id)

    def action_show_error_subjects(self):
        self.change_table("#" + error_subjects_id)

    def construct_job(
        self,
        benchmark: AbstractBenchmark,
        tool: AbstractTool,
        task_profile: Dict[str, Any],
        container_profile: Dict[str, Any],
        experiment_item,
        image_name: Optional[str],
        iteration: int,
        run: str,
        task_config: TaskConfig,
    ):
        tool_tag = task_profile.get(definitions.KEY_TOOL_TAG, "")
        key = main.create_task_identifier(
            benchmark,
            task_profile,
            container_profile,
            experiment_item,
            tool,
            run,
            tool_tag,
        )

        # _ = self.query_one("#" + all_subjects_id, DataTable).add_row(
        #     iteration,
        #     benchmark.name,
        #     tool.name,
        #     experiment_item[definitions.KEY_SUBJECT],
        #     experiment_item[definitions.KEY_BUG_ID],
        #     run,
        #     "N/A" if tool_tag == "" else tool_tag,
        #     task_profile[definitions.KEY_ID],
        #     container_profile[definitions.KEY_ID],
        #     "N/A",
        #     "N/A",
        #     "Allocated",
        #     "N/A",
        #     "N/A",
        #     key=key,
        # )

        log_map[key] = RichLog(highlight=True, markup=True, wrap=True, id=key + "_log")
        self.hide(log_map[key])

        task_type = task_config.task_type
        if not task_type:
            utilities.error_exit("Task type is unassigned!")

        self.post_message(JobMount(key))
        self.post_message(
            JobAllocate(
                iteration,
                deepcopy(benchmark),
                deepcopy(tool),
                experiment_item,
                task_profile,
                container_profile,
                image_name,
                key,
                cast(TaskType, task_type),
                run,
                "N/A" if tool_tag == "" else tool_tag,
                task_config,
            )
        )

    @on(Key)
    async def handle_key_press(self, message: Key):
        if message.key == "escape":
            return
            if self.selected_subject:
                self.hide(log_map[self.selected_subject])
            self.selected_subject = None

    @on(JobAllocate)
    async def on_job_allocate(self, message: JobAllocate):
        loop = asyncio.get_running_loop()

        def job_allocated_job():
            values.task_type.set(cast(TaskType, message.task_type))
            cpus: List[str] = []
            gpus: List[str] = []

            required_cpu_cores = message.container_profile.get(
                definitions.KEY_CONTAINER_CPU_COUNT, message.tool.cpu_usage
            )
            required_gpus = message.container_profile.get(
                definitions.KEY_CONTAINER_GPU_COUNT, message.tool.gpu_usage
            )

            self.update_status(
                message.identifier,
                "Waiting for {} CPU core(s) and {} GPU(s)".format(
                    required_cpu_cores, required_gpus
                ),
            )
            if message.task_config:
                main.process_configs(
                    message.task_config,
                    message.benchmark,
                    message.experiment_item,
                    message.task_profile,
                    message.container_profile,
                )

            with job_condition:
                while (
                    self.free_cpus < required_cpu_cores
                    or self.free_gpus < required_gpus
                ):
                    job_condition.wait()
                if self.jobs_cancelled:
                    self.finished_subjects.append(
                        (message.identifier, TaskStatus.CANCELLED, {}, ToolStats())
                    )
                    job_condition.notify(1)
                    return
                emitter.debug(
                    "Getting {} CPU cores and {} GPUs".format(
                        required_cpu_cores, required_gpus
                    )
                )
                self.free_cpus = self.free_cpus - required_cpu_cores
                self.free_gpus = self.free_gpus - required_gpus
                for _ in range(required_cpu_cores):
                    cpus.append(self.cpu_queue.get(block=True, timeout=None))
                for _ in range(required_gpus):
                    gpus.append(self.gpu_queue.get(block=True, timeout=None))
                if (
                    self.free_cpus > 0
                ):  # Try to wake up another thread if there are more free resources
                    job_condition.notify_all()

            values.job_identifier.set(message.identifier)
            values.current_task_profile_id.set(message.task_profile[definitions.KEY_ID])
            values.current_container_profile_id.set(
                message.container_profile[definitions.KEY_ID]
            )

            self.update_status(message.identifier, "Running")

            start_time = int(time.time())
            start_date = time.ctime()
            timeout = int(
                60
                * 60
                * float(message.task_profile.get(definitions.KEY_CONFIG_TIMEOUT, 1.0))
            )
            # give it more time so things can finish
            timeout = int(timeout + 60 * 1)
            finish_date = time.asctime(time.localtime(float(start_time + timeout)))
            emitter.debug("Setting a timeout of {} seconds".format(timeout))

            job_time_map_mutex.acquire(blocking=True)
            job_time_map[message.identifier] = (
                randint(0, 100000),
                start_time,
                timeout,
                message.tool,
            )
            job_time_map_mutex.release()

            row_data = (
                message.index,
                message.benchmark.name,
                message.tool.name,
                message.experiment_item[definitions.KEY_SUBJECT],
                message.experiment_item[definitions.KEY_BUG_ID],
                message.run,
                message.tag,
                message.task_profile[definitions.KEY_ID],
                message.container_profile[definitions.KEY_ID],
                start_date,
                finish_date,
                "Running",
                "None",
                "N/A",
            )

            # running_row_key = self.query_one(
            #     "#" + running_subjects_id, DataTable
            # ).add_row(
            #     *row_data,
            #     key=message.identifier,
            # )

            # self.query_one("#" + all_subjects_id, DataTable).update_cell(
            #     message.identifier,
            #     Cerberus.COLUMNS[definitions.UI_STARTED_AT][all_subjects_id],
            #     start_date,
            #     update_width=True,
            # )
            # self.query_one("#" + all_subjects_id, DataTable).update_cell(
            #     message.identifier,
            #     Cerberus.COLUMNS[definitions.UI_SHOULD_FINISH][all_subjects_id],
            #     finish_date,
            #     update_width=True,
            # )

            status = TaskStatus.SUCCESS
            dir_info = {}
            try:
                dir_info = task.run(
                    message.benchmark,
                    message.tool,
                    message.experiment_item,
                    message.task_profile,
                    message.container_profile,
                    message.identifier,
                    cpus,
                    gpus,
                    message.experiment_image_id,
                )
            except Exception as e:
                try:
                    job_time_map_mutex.acquire(blocking=True)
                    del job_time_map[message.identifier]
                except Exception as e:
                    pass
                finally:
                    job_time_map_mutex.release()

                log_map[message.identifier].write(traceback.format_exc())
                status = TaskStatus.FAIL
            finally:
                emitter.information(
                    "Finished execution for {}".format(message.identifier)
                )
                # TODO - currently this can crash the system, has to be updated
                # self.call_from_thread(
                #    lambda: self.query_one(
                #        "#" + running_subjects_id, DataTable
                #    ).remove_row(running_row_key)
                # )
                self.post_message(
                    JobFinish(
                        message.identifier,
                        values.experiment_status.get(status),
                        row_data,
                        dir_info["local"] if dir_info else {},
                        message.tool.stats,
                        cast(TaskType, message.task_type),
                    )
                )
            with job_condition:
                for cpu in cpus:
                    self.cpu_queue.put(cpu)
                for gpu in gpus:
                    self.gpu_queue.put(gpu)
                self.free_gpus += required_gpus
                self.free_cpus += required_cpu_cores
                emitter.debug(
                    "Putting back {} CPU cores and {} GPU cores to the job queue".format(
                        required_cpu_cores, required_gpus
                    )
                )
                job_condition.notify_all()

        task_future = loop.run_in_executor(None, job_allocated_job)
        self.jobs[message.identifier] = (task_future, message.tool)

    def update_status(self, key: str, status: str):
        try:  # generally a running task will be updating its status
            # self.query_one("#" + running_subjects_id, DataTable).update_cell(
            #     key,
            #     Cerberus.COLUMNS[definitions.UI_STATUS][running_subjects_id],
            #     status,
            #     update_width=True,
            # )
            pass
        except:
            pass
        try:
            # self.query_one("#" + all_subjects_id, DataTable).update_cell(
            #     key,
            #     Cerberus.COLUMNS[definitions.UI_STATUS][all_subjects_id],
            #     status,
            #     update_width=True,
            # )
            pass
        except:
            pass

    @on(JobMount)
    async def on_mount_job(self, message: JobMount):
        self.debug_print("Mounting {}".format(message.key))
        text_log = log_map[message.key]
        await self.mount(text_log, before=self.query_one("#" + all_subjects_id))
        text_log.write("This is the textual log for {}".format(message.key))
        self.hide(text_log)

    @on(JobFinish)
    async def on_job_finish(self, message: JobFinish):
        def update_table(key, id: str, table: DataTable):
            table.update_cell(
                key,
                Cerberus.COLUMNS[definitions.UI_STATUS][id],
                str(message.status),
                update_width=True,
            )
            table.sort(Cerberus.COLUMNS["ID"][id])
            # TODO temporary
            if message.task_type == "repair":
                table.update_cell(
                    key,
                    Cerberus.COLUMNS[definitions.UI_PLAUSIBLE_PATCHES][id],
                    cast(RepairToolStats, message.results).patch_stats.plausible,
                    update_width=True,
                )
            table.update_cell(
                key,
                Cerberus.COLUMNS[definitions.UI_DURATION][id],
                "{} second(s)".format(message.results.time_stats.get_duration()),
                update_width=True,
            )

        # self.update_status(message.key, str(message.status))
        try:
            # finished_subjects_table = self.query_one(
            #     "#" + finished_subjects_id, DataTable
            # )
            # all_subjects_table = self.query_one("#" + all_subjects_id, DataTable)
            # row_key = finished_subjects_table.add_row(
            #     *message.row_data,
            #     key=message.key,
            # )
            # update_table(row_key, finished_subjects_id, finished_subjects_table)
            pass
            # update_table(message.key, all_subjects_id, all_subjects_table)

            # if message.status is not TaskStatus.SUCCESS:
            #     error_subjects_table = self.query_one(
            #         "#" + error_subjects_id, DataTable
            #     )
            #     row_key = error_subjects_table.add_row(
            #         *message.row_data,
            #         key=message.key,
            #     )
            #     update_table(row_key, error_subjects_id, error_subjects_table)

        except Exception as e:
            self.debug_print(str(e))

        self.jobs_remaining_mutex.acquire(blocking=True)
        self.jobs_remaining -= 1
        self.jobs_remaining_mutex.release()

        self.finished_subjects.append(
            (message.key, message.status, message.directory_info, message.results)
        )

        job_time_map_mutex.acquire(blocking=True)
        if message.key in job_time_map:
            del job_time_map[message.key]
        job_time_map_mutex.release()

        if self.jobs_remaining == 0:
            self.completed_all = True
            self.debug_print("DONE!")
            if not values.debug:
                # Ensure that the job is not counted for twice
                if message.key in self.jobs:
                    del self.jobs[message.key]
                self.exit(self.finished_subjects)

    @on(Write)
    async def write_message(self, message: Write):
        return
        if message.identifier in log_map:
            log_map[message.identifier].write(
                message.text,
                # f"{time.strftime('%b %d %H:%M:%S')} {message.text}",
                shrink=False,
                width=values.ui_max_width,
                scroll_end=(self.selected_subject == message.identifier),
                expand=True,
            )
        self.debug_print(message.text)

    def show(self, x: Widget) -> None:
        x.visible = True
        x.styles.height = "100%"
        x.styles.border = ("heavy", "orange")

    def hide(self, x: Widget) -> None:
        x.visible = False
        x.styles.height = "0%"
        x.styles.border = None

    @on(DataTable.RowHighlighted)
    async def on_data_table_row_highlighted(
        self, message: DataTable.RowHighlighted
    ) -> None:
        # self.debug_print("I am highlighting {}".format(message.row_key.value))
        # self.selected: Optional[str]
        return
        try:
            # if self.selected_subject is not None:
            #     self.hide(log_map[self.selected_subject])
            pass
            # if (
            #     message
            #     and message.row_key
            #     and message.row_key.value
            #     and message.row_key.value in log_map
            # ):
            #     self.selected_subject = message.row_key.value
            #     self.show(log_map[self.selected_subject])
            #     self.set_focus(log_map[self.selected_subject], scroll_visible=True)
            #     log_map[self.selected_subject].scroll_end(animate=False)
            # else:
            #     self.debug_print("Info was not okay? {}".format(message.__dict__))
        except:
            pass

    def compose(self) -> ComposeResult:
        def create_table(id: str):
            table: DataTable = DataTable(id=id)
            table.cursor_type = "row"
            table.styles.border = ("heavy", "orange")
            return table

        """Create child widgets for the app."""
        yield Header()

        static_window = Static("Cerberus is starting")
        static_window.styles.text_align = "center"
        static_window.styles.text_style = "bold italic"

        yield static_window

        all_subjects_table = create_table(all_subjects_id)
        yield all_subjects_table

        self.selected_table = all_subjects_table

        finished_subjects_table = create_table(finished_subjects_id)
        yield finished_subjects_table
        self.hide(finished_subjects_table)

        running_subjects_table = create_table(running_subjects_id)
        yield running_subjects_table
        self.hide(running_subjects_table)

        error_subjects_table = create_table(error_subjects_id)
        yield error_subjects_table
        self.hide(error_subjects_table)

        log_map["root"] = RichLog(highlight=True, markup=True, wrap=True, id="root_log")
        log_map["root"].styles.border = ("heavy", "orange")
        yield log_map["root"]
        if not values.debug:
            self.hide(log_map["root"])

        yield Footer()

    def action_toggle_dark(self) -> None:
        """Toggle dark mode."""
        self.dark: Reactive[bool]
        self.dark = not self.dark  # type: ignore

    def debug_print(self, text: Any):
        if values.debug or self.is_preparing:
            logger.debug(str(text))
            log_map["root"].write(
                text,
                # f"{time.strftime('%b %d %H:%M:%S')} {text}",
                width=values.ui_max_width,
                expand=True,
            )


app: Cerberus


def post_write(text: str):
    return
    message = Write(text=text, identifier=values.job_identifier.get("(Root)"))
    app.post_message(message)


def update_current_job(status: str):
    return
    if not values.ui_active:
        return
    current_job = values.job_identifier.get("NA")
    if current_job != "NA":
        if app._thread_id != threading.get_ident():
            app.call_from_thread(lambda: app.update_status(current_job, status))
        else:
            app.update_status(current_job, status)


def setup_ui(tasks: Optional[TaskList] = None):
    global app
    app = Cerberus()
    app.tasks = tasks
    experiment_results = app.run()
    print_results(experiment_results)
    return len(experiment_results) if experiment_results else 0


def print_results(experiment_results: Optional[List[Result]]):
    values.ui_active = False
    emitter.debug("The final results are {}".format(experiment_results))
    if experiment_results:
        notification.notify(
            "Cerberus has finished running! These are the following results:\n"
            + "\n\n".join(
                map(
                    lambda result: "Experiment {} has final status {}\n logs directory: `{}`\n results directory `{}`\n summary file `{}`".format(
                        result[0],
                        result[1],
                        result[2].get("logs", "N/A"),
                        result[2].get("artifacts", "N/A"),
                        result[2].get("summary", "N/A"),
                    ),
                    experiment_results,
                )
            )
        )

        summary_map = {}
        aggregation_file = join(
            values.dir_summaries, "aggregated_summary_{}.json".format(time.time())
        )
        for experiment, status, dir_info, tool_stats in experiment_results:
            summary_map[experiment] = tool_stats.get_dict()
            emitter.information(
                "\t[framework] Experiment {} has final status {}\n\tlogs directory {}\n\tresults directory {}\n\tsummary file {}\n".format(
                    experiment,
                    status,
                    dir_info.get("logs", "N/A"),
                    dir_info.get("artifacts", "N/A"),
                    dir_info.get("summary", "N/A"),
                )
            )
            summary_map[experiment]["filename"] = aggregation_file
            summary_map[experiment]["dir-info"] = dir_info

        emitter.information(
            "\t[framework] Inserting an aggregation of the data at {}".format(
                aggregation_file
            )
        )

        writer.write_as_json(summary_map, aggregation_file)
