import asyncio
import contextvars
from typing import Any
from typing import Dict
from typing import List
from typing import Optional
from typing import Tuple

from textual.app import App
from textual.app import ComposeResult
from textual.message import Message
from textual.message import MessageTarget
from textual.messages import *
from textual.reactive import Reactive
from textual.reactive import reactive
from textual.screen import Screen
from textual.widgets import DataTable
from textual.widgets import Footer
from textual.widgets import Header
from textual.widgets import Static
from textual.widgets import TextLog

from app.core import configuration
from app.core import definitions
from app.core import emitter
from app.core import main
from app.core import repair
from app.core import utilities
from app.core import values
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool

job_identifier: contextvars.ContextVar[str] = contextvars.ContextVar("job_id")

log_map: Dict[int, TextLog] = {}


class LogScreen(Screen):
    def __init__(self, job_id) -> None:
        self.job_id = job_id
        super().__init__()

    BINDINGS = [("escape", "app.pop_screen", "Pop screen")]

    def compose(self) -> ComposeResult:
        yield Static(" JOB {}".format(self.job_id), id="title")
        yield log_map[self.job_id]
        yield Static("Press any key to exit [blink]_[/]", id="any-key")


class Job(Message):
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


class Write(Message):
    """Write message."""

    namespace = "cerberus"

    def __init__(self, text, identifier):
        self.text = text
        self.identifier = identifier
        super().__init__()


class Cerberus(App):
    """The main window"""

    COLUMNS = (
        "ID",
        "Benchmark",
        "Subject",
        "Bug ID",
        "Configuration Profile",
        "Status",
    )
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
        run_profile_id_list = values.profile_id_list
        for profile_id in run_profile_id_list:
            if profile_id not in setup:
                utilities.error_exit("invalid profile id " + profile_id)
        return tool_list, benchmark, setup

    def on_mount(self):
        values.ui_active = True
        table = self.query_one(DataTable)
        table.cursor_type = "row"
        table.add_columns(*Cerberus.COLUMNS)
        asyncio.get_running_loop().run_in_executor(
            None, lambda: self.run_repair(*self.initialize())
        )

    def run_repair(
        self,
        repair_tool_list: List[AbstractTool],
        benchmark: AbstractBenchmark,
        setup: Any,
    ):
        job_identifier.set("ROOT")
        emitter.sub_title("Repairing benchmark")
        emitter.highlight(
            "[profile] repair-tool(s): " + " ".join([x.name for x in repair_tool_list])
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
                table.add_row(
                    str(iteration),
                    benchmark.name,
                    experiment_item[definitions.KEY_SUBJECT],
                    experiment_item[definitions.KEY_BUG_ID],
                    values.current_profile_id,
                    "Allocated",
                )  # type: ignore
                key = iteration - 1  # "{}-{}-{}-{}".format(
                #    benchmark.name,
                #    "-".join(map(lambda x: x.name, repair_tool_list)),
                #    experiment_item[definitions.KEY_SUBJECT],
                #    experiment_item[definitions.KEY_BUG_ID],
                #    values.current_profile_id,
                # )
                job = Job(
                    benchmark,
                    repair_tool_list,
                    experiment_item,
                    config_info,
                    key,
                )
                log_map[key] = TextLog(highlight=True, markup=True)
                self.post_message(job)

    async def on_cerberus_job(self, message: Job):
        def job():
            job_identifier.set(message.identifier)
            repair.run(
                message.benchmark,
                message.repair_tool_list,
                message.experiment_item,
                message.config_info,
            )

        asyncio.get_running_loop().run_in_executor(None, job)

    async def on_cerberus_write(self, message: Write):
        if message.identifier in log_map:
            log_map[message.identifier].write(message.text)
            log_map[message.identifier].scroll_end()
        pass

    async def on_data_table_row_highlighted(self, message):
        self.push_screen(LogScreen(message.cursor_row))

    def compose(self) -> ComposeResult:
        """Create child widgets for the app."""
        yield Header()
        yield DataTable()
        yield Footer()

    def action_toggle_dark(self) -> None:
        """An action to toggle dark mode."""
        self.dark: Reactive[bool]
        self.dark = not self.dark


app: Cerberus


def get_ui() -> Cerberus:
    return app


def setup_ui():
    global app
    app = Cerberus()
    app.run()
