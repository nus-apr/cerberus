import asyncio
import contextvars
import queue
import traceback
from copy import deepcopy
from enum import Enum
from typing import Any
from typing import Dict
from typing import List
from typing import Optional
from typing import Tuple

from textual.app import App
from textual.app import ComposeResult
from textual.events import Key
from textual.message import Message
from textual.reactive import Reactive
from textual.widget import Widget
from textual.widgets import DataTable
from textual.widgets import Footer
from textual.widgets import Header
from textual.widgets import Static
from textual.widgets import TextLog
from textual.widgets._data_table import ColumnKey

from app.core import configuration
from app.core import definitions
from app.core import email
from app.core import emitter
from app.core import main
from app.core import task
from app.core import utilities
from app.core import values
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool

job_identifier: contextvars.ContextVar[str] = contextvars.ContextVar(
    "job_id", default="root"
)

log_map: Dict[str, TextLog] = {}


class JobAllocate(Message):
    """Job allocation message."""

    bubble = True
    namespace = "cerberus"

    def __init__(
        self,
        benchmark,
        repair_tool_list,
        experiment_item,
        config_info,
        identifier,
    ) -> None:
        self.benchmark = benchmark
        self.repair_tool_list = repair_tool_list
        self.experiment_item = experiment_item
        self.config_info = config_info
        self.identifier = identifier
        super().__init__()


class JobFinish(Message):
    bubble = True
    namespace = "cerberus"

    class Status(Enum):
        SUCCESS = 0
        FAIL = 1

        def __str__(self) -> str:
            if self is self.SUCCESS:
                return "Success"
            elif self is self.FAIL:
                return "Failure"
            else:
                raise NotImplementedError(
                    "New status defined but not implemented in repr"
                )

    def __init__(self, key, status: Status):
        self.key = key
        self.status = status
        super().__init__()


class JobMount(Message):
    bubble = False
    namespace = "cerberus"

    def __init__(self, key):
        self.key = key
        super().__init__()


class Write(Message):
    """Write message."""

    namespace = "cerberus"

    def __init__(self, text, identifier):
        self.text = text
        self.identifier = identifier
        super().__init__()


class Cerberus(App[List[Tuple[str, JobFinish.Status]]]):
    """The main window"""

    COLUMNS: Dict[str, Optional[ColumnKey]] = {
        "ID": None,
        "Benchmark": None,
        "Tool list": None,
        "Subject": None,
        "Bug ID": None,
        "Configuration Profile": None,
        "Status": None,
    }

    SUB_TITLE = "Program Repair Framework"

    BINDINGS = [
        ("d", "toggle_dark", "Toggle dark mode"),
        ("f", "show_finished", "Show Finished Subjects"),
        ("r", "show_running", "Show Running Subjects"),
        ("a", "show_all_subjects", "Show All Subjects"),
    ]

    def on_exit(self):
        values.ui_active = False

    def on_mount(self):
        self.selected_subject = None
        self.jobs_remaining = 0
        self.finished_subjects = []
        self.jobs: List[asyncio.Future] = []
        self.max_jobs = values.cpus
        self.cpu_queue = queue.Queue(self.max_jobs + 1)
        for cpu in range(self.max_jobs):
            self.cpu_queue.put(cpu)
        asyncio.get_running_loop().set_exception_handler(self.handle)
        values.ui_active = True

        column_keys = self.query_one(DataTable).add_columns(*Cerberus.COLUMNS.keys())
        for (k, v) in zip(Cerberus.COLUMNS.keys(), column_keys):
            Cerberus.COLUMNS[k] = v
        asyncio.get_running_loop().run_in_executor(
            None,
            self.pre_run,
        )

    def pre_run(self):
        try:
            self.query_one(DataTable).visible = False

            self.query_one(Static).update("Cerberus is getting tools")
            tools = main.get_tools()

            self.query_one(Static).update("Cerberus is getting the benchmark")
            benchmark = main.get_benchmark()

            self.query_one(Static).update("Cerberus is getting the setup data")
            setup = main.get_setup()

            self.hide(self.query_one(Static))

            self.query_one(DataTable).visible = True
            self.query_one(DataTable).styles.height = "100%"
            self.run_tasks(tools, benchmark, setup)
        except Exception as e:
            self.show(self.query_one(Static))
            self.query_one(Static).update(
                "{}\n{}".format(str(e), traceback.format_exc())
            )
            self.debug_print("I got exception {}".format(e))

    async def show_finished(self):
        pass

    async def show_running(self):
        pass

    async def show_all_subjects(self):
        pass

    def handle(self, a, b):
        self.debug_print("GOT EXCEPTION!")
        pass

    def run_tasks(
        self,
        tool_list: List[AbstractTool],
        benchmark: AbstractBenchmark,
        setup: Any,
    ):
        iteration = 0
        for config_info in map(lambda x: setup[x], values.profile_id_list):
            for experiment_item in main.filter_experiment_list(benchmark):
                iteration = iteration + 1
                bug_index = experiment_item[definitions.KEY_ID]
                emitter.sub_sub_title(
                    "Experiment #{} - Bug #{}".format(iteration, bug_index)
                )
                utilities.check_space()
                key = "{}-{}-{}-{}-{}".format(
                    benchmark.name,
                    "-".join(map(lambda x: x.name, tool_list)),
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                    config_info[definitions.KEY_ID],
                )

                _ = self.query_one(DataTable).add_row(
                    str(iteration),
                    benchmark.name,
                    ",".join(map(lambda t: t.name, tool_list)),
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                    config_info[definitions.KEY_ID],
                    "Allocated",
                    key=key,
                )

                log_map[key] = TextLog(highlight=True, markup=True)
                log_map[key].visible = False
                log_map[key].auto_height = True

                self.post_message(JobMount(key))
                self.post_message(
                    JobAllocate(
                        deepcopy(benchmark),
                        [deepcopy(x) for x in tool_list],
                        experiment_item,
                        config_info,
                        key,
                    )
                )
        self.jobs_remaining = iteration

    async def on_key(self, message: Key):
        # self.debug_print("I am seeing? {}".format(message))
        if message.key == "escape":
            if self.selected_subject:
                self.hide(log_map[self.selected_subject])
            self.selected_subject = None
            # self.set_focus(self.query_one(DataTable))

    async def on_cerberus_job_allocate(self, message: JobAllocate):
        def job():
            self.update_status(message.identifier, "Waiting for CPU")
            cpus = []
            for _ in range(max([x.cpu_usage for x in message.repair_tool_list])):
                cpus.append(self.cpu_queue.get(block=True, timeout=None))
            job_identifier.set(message.identifier)
            values.current_profile_id.set(message.config_info[definitions.KEY_ID])

            self.update_status(message.identifier, "Running")
            try:
                task.run(
                    message.benchmark,
                    message.repair_tool_list,
                    message.experiment_item,
                    message.config_info,
                    message.identifier,
                    ",".join(map(str, cpus)),
                )
            except Exception as e:
                self.post_message(
                    Write(
                        "Error {}\n{}".format(e, traceback.format_exc()),
                        message.identifier,
                    )
                )
                self.post_message(JobFinish(message.identifier, JobFinish.Status.FAIL))
            finally:
                self.post_message(Write("Finished", message.identifier))
            for cpu in cpus:
                self.cpu_queue.put(cpu)

        self.jobs.append(asyncio.get_running_loop().run_in_executor(None, job))

    def update_status(self, key, status):
        if Cerberus.COLUMNS["Status"]:
            self.query_one(DataTable).update_cell(
                key, Cerberus.COLUMNS["Status"], status
            )

    async def on_cerberus_job_mount(self, message: JobMount):
        self.debug_print("Mounting {}".format(message.key))
        text_log = log_map[message.key]
        await self.mount(text_log, before=self.query_one(DataTable))
        text_log.write("This is the textual log for {}".format(message.key))
        self.hide(text_log)
        text_log.styles.border = ("heavy", "white")

    async def on_cerberus_job_finish(self, message: JobFinish):
        self.update_status(message.key, str(message.status))
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
                scroll_end=False,
                expand=log_map[message.identifier].visible,
            )
        self.debug_print(message.text)

    def show(self, x: Widget):
        x.visible = True
        x.styles.height = "100%"

    def hide(self, x: Widget):
        x.visible = False
        x.styles.height = "0%"

    async def on_data_table_row_highlighted(self, message: DataTable.RowHighlighted):
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
        """Create child widgets for the app."""
        yield Header()
        yield Static("Cerberus is starting")
        table: DataTable[Any] = DataTable()
        table.cursor_type = "row"
        table.styles.border = ("heavy", "white")
        yield table

        if values.debug:
            log_map["root"] = TextLog(highlight=True, markup=True)
            log_map["root"].styles.border = ("heavy", "white")
            yield log_map["root"]

        yield Footer()

    def action_toggle_dark(self) -> None:
        """Toggle dark mode."""
        self.dark: Reactive[bool]
        self.dark = not self.dark  # type: ignore

    def debug_print(self, text: Any):
        if values.debug:
            log_map["root"].write(text)


app: Cerberus


def get_ui() -> Cerberus:
    return app


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
