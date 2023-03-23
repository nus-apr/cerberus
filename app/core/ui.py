import asyncio
import contextvars
from copy import copy
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
from textual.widgets import TextLog
from textual.widgets._data_table import ColumnKey

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import main
from app.core import repair
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


class Cerberus(App):
    """The main window"""

    COLUMNS: Dict[str, Optional[ColumnKey]] = {
        "ID": None,
        "Benchmark": None,
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

    def initialize(self) -> Tuple[List[AbstractTool], AbstractBenchmark, Any]:
        emitter.sub_title("Initializing setup")
        tool_list = []
        if values.tool_list:
            for tool_name in values.tool_list:
                tool = configuration.load_tool(tool_name)
                if not values.only_analyse:
                    tool.check_tool_exists()
                tool_list.append(tool)
        benchmark = configuration.load_benchmark(values.benchmark_name.lower())
        setup = configuration.load_configuration_details(values.file_configuration)
        for profile_id in values.profile_id_list:
            if profile_id not in setup:
                utilities.error_exit("Invalid profile id {}".format(profile_id))
        return tool_list, benchmark, setup

    def on_mount(self):
        self.selected = None
        self.jobs = 0
        asyncio.get_running_loop().set_exception_handler(self.handle)
        values.ui_active = True
        table = self.query_one(DataTable)
        table.cursor_type = "row"

        vals = table.add_columns(*Cerberus.COLUMNS.keys())
        for (k, v) in zip(Cerberus.COLUMNS.keys(), vals):
            Cerberus.COLUMNS[k] = v
        asyncio.get_running_loop().run_in_executor(
            None, lambda: self.run_repair(*self.initialize())
        )

    async def show_finished(self):
        table = self.query_one(DataTable)
        pass

    async def show_running(self):
        pass

    async def show_all_subjects(self):
        pass

    def handle(self, a, b):
        self.debug_print("GOT EXCEPTION!")
        pass

    def run_repair(
        self,
        repair_tool_list: List[AbstractTool],
        benchmark: AbstractBenchmark,
        setup: Any,
    ):
        emitter.sub_title("Repairing benchmark")
        emitter.highlight(
            "(profile) repair-tool(s): " + " ".join([x.name for x in repair_tool_list])
        )
        emitter.highlight("(profile) repair-benchmark: " + benchmark.name)
        iteration = 0
        for profile_id in values.profile_id_list:
            config_info = setup[profile_id]
            values.current_profile_id = config_info[definitions.KEY_ID]
            for experiment_item in main.filter_experiment_list(benchmark):
                iteration = iteration + 1
                values.iteration_no = iteration
                bug_index = experiment_item[definitions.KEY_ID]
                emitter.sub_sub_title(
                    "Experiment #{} - Bug #{}".format(iteration, bug_index)
                )
                utilities.check_space()
                table = self.query_one(DataTable)
                key = "{}-{}-{}-{}-{}".format(
                    benchmark.name,
                    "-".join(map(lambda x: x.name, repair_tool_list)),
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                    values.current_profile_id,
                )

                _ = table.add_row(
                    str(iteration),
                    benchmark.name,
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                    values.current_profile_id,
                    "Allocated",
                    key=key,
                )

                job = JobAllocate(
                    benchmark,
                    [copy(x) for x in repair_tool_list],
                    experiment_item,
                    config_info,
                    key,
                )
                log_map[key] = TextLog(highlight=True, markup=True)
                log_map[key].visible = False
                log_map[key].auto_height = True
                self.post_message(JobMount(key))
                self.post_message(job)
        self.jobs = iteration

    async def on_key(self, message: Key):
        self.debug_print("I am seeing? {}".format(message))
        if message.key == "escape":
            if self.selected:
                self.hide(log_map[self.selected])
            self.selected = None
            # self.set_focus(self.query_one(DataTable))

    async def on_cerberus_job_allocate(self, message: JobAllocate):
        def job():
            job_identifier.set(message.identifier)
            repair.run(
                message.benchmark,
                message.repair_tool_list,
                message.experiment_item,
                message.config_info,
                message.identifier,
            )

        asyncio.get_running_loop().run_in_executor(None, job)

    async def on_cerberus_job_mount(self, message: JobMount):
        self.debug_print("Mounting {}".format(message.key))
        text_log = log_map[message.key]
        await self.mount(text_log, before=self.query_one(DataTable))
        self.hide(text_log)
        text_log.styles.border = ("heavy", "white")

    async def on_cerberus_job_finish(self, message: JobFinish):
        if Cerberus.COLUMNS["Status"]:
            self.query_one(DataTable).update_cell(
                message.key, Cerberus.COLUMNS["Status"], str(message.status)
            )
        self.jobs -= 1
        if self.jobs == 0:
            await self.action_quit()

    async def on_cerberus_write(self, message: Write):
        if message.identifier in log_map:
            log_map[message.identifier].write(message.text)
        self.debug_print(message.text)

    def show(self, x: Widget):
        x.visible = True
        x.styles.height = "100%"

    def hide(self, x: Widget):
        x.visible = False
        x.styles.height = "0%"

    async def on_data_table_row_highlighted(self, message: DataTable.RowHighlighted):
        self.debug_print("I am highlighting {}".format(message.row_key.value))
        # self.selected: Optional[str]
        if self.selected is not None:
            log_map["root"].write("Selected is not none but {}".format(self.selected))
            self.hide(log_map[self.selected])

        if message.row_key.value:
            self.selected = message.row_key.value
            self.show(log_map[self.selected])
            self.set_focus(log_map[self.selected])

    def compose(self) -> ComposeResult:
        """Create child widgets for the app."""
        yield Header()
        table: DataTable[Any] = DataTable()
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
    app.run()
