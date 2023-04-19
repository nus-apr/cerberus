import asyncio
import queue
import signal
import threading
import time
import traceback
from copy import deepcopy
from typing import Any
from typing import Dict
from typing import List
from typing import Tuple

from textual.app import App
from textual.app import ComposeResult
from textual.events import Key
from textual.reactive import Reactive
from textual.widget import Widget
from textual.widgets import DataTable
from textual.widgets import Footer
from textual.widgets import Header
from textual.widgets import Static
from textual.widgets import TextLog
from textual.widgets._data_table import ColumnKey

from app.core import container
from app.core import definitions
from app.core import emitter
from app.core import main
from app.core import utilities
from app.core import values
from app.core.task import task
from app.core.task.status import TaskStatus
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool
from app.notification import email
from app.ui.datatable import CustomDataTable
from app.ui.messages import JobAllocate
from app.ui.messages import JobFinish
from app.ui.messages import JobMount
from app.ui.messages import Write

all_subjects_id = "all_subjects"
finished_subjects_id = "finished_subjects"
error_subjects_id = "error_subjects"
running_subjects_id = "running_subjects"

log_map: Dict[str, TextLog] = {}
time_map: Dict[str, Tuple[float, float, AbstractTool]] = {}


class Cerberus(App[List[Tuple[str, TaskStatus]]]):
    """The main window"""

    COLUMNS: Dict[str, Dict[str, ColumnKey]] = {
        "ID": {},
        "Benchmark": {},
        "Tool": {},
        "Subject": {},
        "Bug ID": {},
        "Repair Configuration Profile": {},
        "Container Configuration Profile": {},
        "Status": {},
        "Patches Generated": {},
    }

    SUB_TITLE = "Program Repair Framework"

    BINDINGS = [
        ("d", "toggle_dark", "Toggle dark mode"),
        ("a", "show_all_subjects", "Show All Subjects"),
        ("r", "show_running_subjects", "Show Running Subjects"),
        ("f", "show_finished_subjects", "Show Finished Subjects"),
        ("e", "show_error_subjects", "Show Erred Subjects"),
    ]

    def on_exit(self):
        values.ui_active = False

    def on_mount(self):
        self.selected_subject = None
        self.jobs_remaining = 0
        self.finished_subjects = []
        self.jobs: Dict[str, asyncio.Future] = {}

        self.setup_cpu_allocation()

        values.ui_active = True

        self.setup_column_keys()

        loop = asyncio.get_running_loop()
        asyncio.get_running_loop().run_in_executor(None, self.prepare_run, loop)

    def setup_cpu_allocation(self):
        self.max_jobs = values.cpus
        self.cpu_queue: queue.Queue[int] = queue.Queue(self.max_jobs + 1)
        for cpu in range(self.max_jobs):
            self.cpu_queue.put(cpu)

    def setup_column_keys(self):
        for table in self.query(CustomDataTable):
            column_keys = table.add_columns(*Cerberus.COLUMNS.keys())
            if not table.id:
                utilities.error_exit(
                    "CustomDataTable does not have ID. This should not happen"
                )
            for (column_name, column_key) in zip(Cerberus.COLUMNS.keys(), column_keys):
                Cerberus.COLUMNS[column_name][table.id] = column_key

    def _on_idle(self) -> None:
        super()._on_idle()
        # self.debug_print("Idle")
        now = time.time()
        to_del = []
        for (k, v) in time_map.items():
            (start, limit, tool) = v
            if now - start > limit:
                if not self.jobs[k].done():
                    self.debug_print("TIME TO KILL {}".format(v))
                    log_map[k].write("KILLED BY WATCHDOG")
                    if tool.container_id:
                        log_map["root"].write("Killing {}".format(tool.container_id))
                        # Currently this kills the container and the tool gets a 137 status for the run command
                        # Possibly we can also track a "critical" section of the tool run
                        # as killing it outside of that specific moment does not seem sensible
                        container.stop_container(tool.container_id)
                    else:
                        emitter.information(
                            "Cannot kill a local process as I do not know the exact process id"
                        )
                    log_map[k].write("Cancelled")
                to_del.append(k)

        for k in to_del:
            del time_map[k]

    def prepare_run(self, loop):
        try:
            self.hide(self.query_one("#" + all_subjects_id))

            self.is_preparing = True

            self.show(log_map["root"])
            self.query_one(Static).update("Cerberus is preparing tool images")
            tools = main.get_tools()

            self.query_one(Static).update("Cerberus is preparing the benchmark image")
            benchmark = main.get_benchmark()

            self.query_one(Static).update("Cerberus is getting setup data")
            setup = main.get_repair_setup()

            self.query_one(Static).update("Cerberus is getting container setup data")
            container_setup = main.get_container_setup()

            if values.use_container:
                self.query_one(Static).update(
                    "Cerberus is preparing the subject images."
                )
                complete_images: queue.Queue[Tuple[Any, bool]] = queue.Queue(0)

                def job(benchmark: AbstractBenchmark, experiment_item):
                    cpu = self.cpu_queue.get(block=True, timeout=None)
                    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
                    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
                    values.job_identifier.set(
                        "{}-{}-{}".format(benchmark.name, subject_name, bug_name)
                    )
                    dir_info = task.generate_dir_info(
                        benchmark.name, subject_name, bug_name
                    )
                    benchmark.update_dir_info(dir_info)
                    try:
                        benchmark.get_exp_image(
                            experiment_item[definitions.KEY_ID],
                            values.only_test,
                            str(cpu),
                        )
                        complete_images.put((experiment_item[definitions.KEY_ID], True))
                    except:
                        complete_images.put(
                            (experiment_item[definitions.KEY_ID], False)
                        )
                    finally:
                        self.cpu_queue.put(cpu, block=False)

                all_experiment_jobs = main.filter_experiment_list(benchmark)
                for experiment_item in all_experiment_jobs:
                    loop.run_in_executor(
                        None, job, deepcopy(benchmark), experiment_item
                    )
                    # benchmark.get_exp_image(experiment_item[definitions.KEY_ID], values.only_test, "1")
                while complete_images.qsize() != len(all_experiment_jobs):
                    pass
                while complete_images.qsize() != 0:
                    (id, success) = complete_images.get()
                    if not success:
                        emitter.warning("[warning] Failed building image {}".format(id))

            self.hide(self.query_one(Static))
            if not values.debug:
                self.hide(log_map["root"])
            self.is_preparing = False

            self.show(self.query_one("#" + all_subjects_id))
            self.run_tasks(tools, benchmark, setup, container_setup)
        except Exception as e:
            self.show(self.query_one(Static))
            self.query_one(Static).update(
                "{}\n{}".format(str(e), traceback.format_exc())
            )
            self.debug_print("I got exception {}".format(e))

    def change_table(self, new_id):
        if self.is_preparing:
            return
        self.debug_print("Changing table!")
        try:
            self.selected_table: CustomDataTable

            self.hide(self.selected_table)

            self.selected_table = self.query_one(new_id, CustomDataTable)

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

    def run_tasks(
        self,
        tool_list: List[AbstractTool],
        benchmark: AbstractBenchmark,
        repair_setup: Any,
        container_setup: Any,
    ):
        utilities.check_space()
        iteration = 0
        for container_config_info in map(
            lambda x: container_setup[x], values.container_profile_id_list
        ):
            for repair_config_info in map(
                lambda x: repair_setup[x], values.repair_profile_id_list
            ):
                for experiment_item in main.filter_experiment_list(benchmark):
                    bug_index = experiment_item[definitions.KEY_ID]

                    # The experiment should be built at this point, hardcoded cpu should not be a problem
                    experiment_image_id = (
                        benchmark.get_exp_image(bug_index, values.only_test, "0")
                        if values.use_container
                        else None
                    )

                    for tool in tool_list:
                        iteration = iteration + 1
                        emitter.sub_sub_title(
                            "Experiment #{} - Bug #{} Tool {}".format(
                                iteration, bug_index, tool.name
                            )
                        )
                        key = "{}-{}-{}-{}-{}-{}".format(
                            benchmark.name,
                            tool.name,
                            experiment_item[definitions.KEY_SUBJECT],
                            experiment_item[definitions.KEY_BUG_ID],
                            repair_config_info[definitions.KEY_ID],
                            container_config_info[definitions.KEY_ID],
                        )

                        _ = self.query_one(
                            "#" + all_subjects_id, CustomDataTable
                        ).add_row(
                            iteration,
                            benchmark.name,
                            tool.name,
                            experiment_item[definitions.KEY_SUBJECT],
                            experiment_item[definitions.KEY_BUG_ID],
                            repair_config_info[definitions.KEY_ID],
                            container_config_info[definitions.KEY_ID],
                            "Allocated",
                            "None",
                            key=key,
                        )

                        log_map[key] = TextLog(highlight=True, markup=True, wrap=True)
                        self.hide(log_map[key])

                        self.post_message(JobMount(key))
                        self.post_message(
                            JobAllocate(
                                iteration,
                                deepcopy(benchmark),
                                deepcopy(tool),
                                experiment_item,
                                repair_config_info,
                                container_config_info,
                                experiment_image_id,
                                key,
                            )
                        )
            self.jobs_remaining = iteration

    async def on_key(self, message: Key):
        if message.key == "escape":
            if self.selected_subject:
                self.hide(log_map[self.selected_subject])
            self.selected_subject = None

    async def on_cerberus_job_allocate(self, message: JobAllocate):
        loop = asyncio.get_running_loop()

        def job():
            self.update_status(message.identifier, "Waiting for CPU")
            cpus: List[int] = []
            for _ in range(
                message.container_config_info.get(
                    definitions.KEY_CONTAINER_CPU_COUNT, message.tool.cpu_usage
                )
            ):
                cpus.append(self.cpu_queue.get(block=True, timeout=None))
            values.job_identifier.set(message.identifier)
            values.current_repair_profile_id.set(
                message.repair_config_info[definitions.KEY_ID]
            )
            values.current_container_profile_id.set(
                message.container_config_info[definitions.KEY_ID]
            )

            self.update_status(message.identifier, "Running")

            row_data = (
                message.index,
                message.benchmark.name,
                message.tool.name,
                message.experiment_item[definitions.KEY_SUBJECT],
                message.experiment_item[definitions.KEY_BUG_ID],
                message.repair_config_info[definitions.KEY_ID],
                message.container_config_info[definitions.KEY_ID],
                "Running",
                "None",
            )

            running_row_key = self.query_one(
                "#" + running_subjects_id, CustomDataTable
            ).add_row(
                *row_data,
                key=message.identifier,
            )

            status = TaskStatus.SUCCESS
            try:
                time_map[message.identifier] = (
                    time.time(),
                    60
                    * 60
                    * float(
                        message.repair_config_info.get(
                            definitions.KEY_CONFIG_TIMEOUT, 1.0
                        )
                    ),
                    message.tool,
                )
                cpu_set = ",".join(map(str, cpus))
                task.run(
                    message.benchmark,
                    message.tool,
                    message.experiment_item,
                    message.repair_config_info,
                    message.container_config_info,
                    message.identifier,
                    cpu_set,
                    message.experiment_image_id,
                )
            except Exception as e:
                log_map[message.identifier].write(traceback.format_exc())
                status = TaskStatus.FAIL
            finally:
                emitter.information(
                    "Finished execution for {}".format(message.identifier)
                )
                self.call_from_thread(
                    lambda: self.query_one(
                        "#" + running_subjects_id, CustomDataTable
                    ).remove_row(running_row_key)
                )
                self.post_message(
                    JobFinish(
                        message.identifier,
                        values.experiment_status.get(status),
                        row_data,
                    )
                )
            for cpu in cpus:
                self.cpu_queue.put(cpu)

        task_future = loop.run_in_executor(None, job)
        self.jobs[message.identifier] = task_future

    def update_status(self, key: str, status: str):
        if self.selected_table.id:
            self.selected_table.update_cell(
                key,
                Cerberus.COLUMNS["Status"][self.selected_table.id],
                status,
                update_width=True,
            )
        self.query_one("#" + all_subjects_id, CustomDataTable).update_cell(
            key,
            Cerberus.COLUMNS["Status"][all_subjects_id],
            status,
            update_width=True,
        )

    async def on_cerberus_job_mount(self, message: JobMount):
        self.debug_print("Mounting {}".format(message.key))
        text_log = log_map[message.key]
        await self.mount(text_log, before=self.query_one("#" + all_subjects_id))
        text_log.write("This is the textual log for {}".format(message.key))
        self.hide(text_log)

    async def on_cerberus_job_finish(self, message: JobFinish):
        # self.update_status(message.key, str(message.status))
        try:
            finished_subjects_table = self.query_one(
                "#" + finished_subjects_id, CustomDataTable
            )
            all_subjects_table = self.query_one("#" + all_subjects_id, CustomDataTable)
            row_key = finished_subjects_table.add_row(
                *message.row_data,
                key=message.key,
            )
            finished_subjects_table.update_cell(
                row_key,
                Cerberus.COLUMNS["Status"][finished_subjects_id],
                str(message.status),
            )
            finished_subjects_table.sort(Cerberus.COLUMNS["ID"][finished_subjects_id])

            all_subjects_table.update_cell(
                row_key,
                Cerberus.COLUMNS["Status"][all_subjects_id],
                str(message.status),
            )
            if message.status is not TaskStatus.SUCCESS:
                error_subjects_table = self.query_one(
                    "#" + error_subjects_id, CustomDataTable
                )
                row_key = error_subjects_table.add_row(
                    *message.row_data,
                    key=message.key,
                )
                error_subjects_table.update_cell(
                    row_key,
                    Cerberus.COLUMNS["Status"][error_subjects_id],
                    str(message.status),
                )

        except Exception as e:
            self.debug_print(str(e))

        self.jobs_remaining -= 1
        self.finished_subjects.append((message.key, message.status))
        if self.jobs_remaining == 0:
            self.debug_print("DONE!")
            # self.exit(self.finished_subjects)

    async def on_cerberus_write(self, message: Write):
        if message.identifier in log_map:
            log_map[message.identifier].write(
                message.text,
                shrink=False,
                width=values.ui_max_width,
                scroll_end=(self.selected_subject == message.identifier),
                expand=True,
            )
        self.debug_print(message.text)

    def show(self, x: Widget) -> None:
        x.visible = True
        x.styles.height = "100%"
        x.styles.border = ("heavy", "white")

    def hide(self, x: Widget) -> None:
        x.visible = False
        x.styles.height = "0%"
        x.styles.border = None

    async def on_data_table_row_highlighted(
        self, message: DataTable.RowHighlighted
    ) -> None:
        # self.debug_print("I am highlighting {}".format(message.row_key.value))
        # self.selected: Optional[str]
        if self.selected_subject is not None:
            self.hide(log_map[self.selected_subject])

        if message.row_key.value:
            self.selected_subject = message.row_key.value
            self.show(log_map[self.selected_subject])
            self.set_focus(log_map[self.selected_subject])
            log_map[self.selected_subject].scroll_end(animate=False)

    def compose(self) -> ComposeResult:
        def create_table(id: str):
            table: CustomDataTable = CustomDataTable(id=id)
            table.cursor_type = "row"
            table.styles.border = ("heavy", "white")
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

        log_map["root"] = TextLog(highlight=True, markup=True, wrap=True)
        log_map["root"].styles.border = ("heavy", "white")
        yield log_map["root"]
        if not values.debug:
            self.hide(log_map["root"])

        yield Footer()

    def action_toggle_dark(self) -> None:
        """Toggle dark mode."""
        self.dark: bool
        self.dark = not self.dark

    def debug_print(self, text: Any):
        if values.debug or self.is_preparing:
            log_map["root"].write(text, width=values.ui_max_width, expand=True)


app: Cerberus


def post_write(text: str):
    message = Write(text=text, identifier=values.job_identifier.get("(Root)"))
    if app._thread_id != threading.get_ident():
        app.call_from_thread(lambda: app.post_message(message))
    else:
        app.post_message(message)


def update_current_job(status: str):
    current_job = values.job_identifier.get("NA")
    if current_job != "NA":
        if app._thread_id != threading.get_ident():
            app.call_from_thread(lambda: app.update_status(current_job, status))
        else:
            app.update_status(current_job, status)


def setup_ui():
    global app
    app = Cerberus()
    experiment_results = app.run()
    emitter.debug("The final results are {}".format(experiment_results))
    if experiment_results:
        values.iteration_no = len(experiment_results)
        email.send_message(
            "Cerberus has finished running! These are the following results:\n"
            + "\n".join(map(lambda t: "{} -> {}".format(*t), experiment_results))
        )
        for (experiment, status) in experiment_results:
            emitter.information(
                "Experiment {} has final status {}".format(experiment, status)
            )
