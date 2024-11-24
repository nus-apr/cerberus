# -*- coding: utf-8 -*-
import os
import random
import sys
import textwrap
import time
from enum import Enum
from typing import Any
from typing import List
from typing import Optional
from typing import Union

import rich

from app.core import definitions
from app.core import logger
from app.core import values
from app.ui import ui

try:
    stty_info = os.popen("stty size", "r")
    rows, columns = tuple(map(int, stty_info.read().split()))
    stty_info.close()
except Exception as e:
    rows, columns = 500, 800
    rich.print("Could not get terminal size: {}".format(e))


class COLOR(Enum):
    GREY = 1
    RED = 2
    GREEN = 3
    YELLOW = 4
    BLUE = 4
    ROSE = 5
    CYAN = 6
    WHITE = 7
    PROG_OUTPUT_COLOR = 8
    STAT_COLOR = 9


RICH_COLOR_MAP = {
    COLOR.GREY: "grey",
    COLOR.RED: "red",
    COLOR.GREEN: "green",
    COLOR.YELLOW: "yellow",
    COLOR.BLUE: "blue",
    COLOR.ROSE: "rose",
    COLOR.CYAN: "cyan",
    COLOR.WHITE: "none",
    COLOR.PROG_OUTPUT_COLOR: "blue",
    COLOR.STAT_COLOR: "green",
}

TEXTUALIZE_COLOR_MAP = {
    COLOR.GREY: "grey",
    COLOR.RED: "$error",
    COLOR.GREEN: "$success",
    COLOR.YELLOW: "$warning",
    COLOR.BLUE: "blue",
    COLOR.ROSE: "pink",
    COLOR.CYAN: "cyan",
    COLOR.WHITE: "$primary",
    COLOR.PROG_OUTPUT_COLOR: "green",
    COLOR.STAT_COLOR: "green",
}


def write(
    print_message: Any,
    print_color: COLOR,
    new_line: bool = True,
    prefix: Optional[str] = None,
    indent_level: int = 0,
) -> None:
    timestamp_str = (
        "" if not values.timestamp else f" {time.strftime('%b %d %H:%M:%S')}"
    )
    if not values.ui_active:
        message = "[bold {}]{}".format(
            RICH_COLOR_MAP[print_color],
            str(print_message).replace("[", "\\["),
        )
        if prefix:
            prefix = "[{}]{}".format(RICH_COLOR_MAP[print_color], prefix)
            len_prefix = ((indent_level + 1) * 4) + len(prefix)
            wrapper = textwrap.TextWrapper(
                initial_indent=prefix,
                subsequent_indent=" " * len_prefix,
                width=int(columns),
            )
            message = wrapper.fill(message)
        rich.print(message, end=("\n" if new_line else "\r"))
    else:
        if prefix:
            print_message = prefix + str(print_message)

        ui.post_write(
            "[bold {}]{} {}{}".format(
                TEXTUALIZE_COLOR_MAP[print_color],
                values.job_identifier.get("Root"),
                str(print_message).replace("[", "\\[").replace("\t", " "),
                timestamp_str,
            )
        )


def title(title: str) -> None:
    write("\n" + "=" * 100 + "\n\n\t" + title + "\n" + "=" * 100 + "\n", COLOR.CYAN)
    logger.information(title)


def sub_title(text: str) -> None:
    write("\n\t" + text + "\n\t" + "_" * 90 + "\n", COLOR.CYAN)
    logger.information(text)


def sub_sub_title(text: str) -> None:
    write("\n\t\t" + text + "\n\t\t" + "_" * 90 + "\n", COLOR.CYAN)
    logger.information(text)


def command(message: Any) -> None:
    if values.debug:
        prefix = "\t\t[command] "
        write(message, COLOR.ROSE, prefix=prefix, indent_level=2)
    logger.command(message)


def docker_command(message: Any) -> None:
    if values.debug:
        prefix = "\t\t[docker-command] "
        write(message, COLOR.ROSE, prefix=prefix, indent_level=2)
    logger.docker_command(message)


def debug(message: Any) -> None:
    if values.debug:
        prefix = "\t\t[debug] "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.debug(message)


def build(message: Any) -> None:
    if values.debug:
        prefix = "\t\t[build] "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.build(message)


def data(message: Any, info: Any = None) -> None:
    if values.debug:
        prefix = "\t\t[data] "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
        if info:
            write(info, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.data(message, info)


def normal(message: Any, jump_line: bool = True) -> None:
    write(message, COLOR.BLUE, jump_line, prefix="\t\t[normal] ")
    logger.output(message)


def highlight(message: Any, jump_line: bool = True) -> None:
    indent_length = message.count("\t")
    prefix = "\t" * indent_length
    message = message.replace("\t", "")
    write(message, COLOR.WHITE, jump_line, indent_level=indent_length, prefix=prefix)
    logger.note(message)


def information(message: Any, jump_line: bool = True) -> None:
    write(message, COLOR.GREY, jump_line, prefix="[info]")
    logger.information(message)


def statistics(message: Any) -> None:
    write(message, COLOR.WHITE, prefix="[stat]")
    logger.output(message)


def error(message: Any) -> None:
    write(message, COLOR.RED, prefix="[error]")
    logger.error(message)


def success(message: Any) -> None:
    write(message, COLOR.GREEN, prefix="[info]")
    logger.output(message)


def special(message: Any) -> None:
    write(message, COLOR.ROSE, prefix="[special]")
    logger.note(message)


def program_output(output_message: Union[str, List[str]]) -> None:
    write("\t\tProgram Output:", COLOR.WHITE)
    if type(output_message) == list:
        for line in output_message:
            write("\t\t\t" + line.strip(), COLOR.PROG_OUTPUT_COLOR)
    elif type(output_message) == str:
        write("\t\t\t" + output_message, COLOR.PROG_OUTPUT_COLOR)


def emit_patch(
    patch_lines: List[str], jump_line: bool = True, message: str = ""
) -> None:
    indent_length = 2
    prefix = "\t\t" * indent_length
    write(message, COLOR.WHITE, jump_line, indent_level=indent_length, prefix=prefix)
    for line in patch_lines:
        write(line, COLOR.ROSE, jump_line, indent_level=indent_length, prefix=prefix)


def warning(message: Any) -> None:
    write(message, COLOR.YELLOW, prefix="[warning]")
    logger.warning(message)


def note(message: Any) -> None:
    write(message, COLOR.WHITE, prefix="[note]")
    logger.note(message)


def configuration(setting: str, value: Any) -> None:
    message = "\t[config] " + setting + ": " + str(value)
    write(message, COLOR.WHITE, True)
    logger.configuration(setting + ":" + str(value))


def end(time_total: str, experiments_executed: int, is_error: bool = False) -> None:
    if values.arg_pass:
        statistics("\nRun time statistics:\n-----------------------\n")
        statistics("Experiment Count: {}".format(experiments_executed))
        action = error if is_error else success
        text = "exited with an error" if is_error else "finished successfully"

        action("\n {} {} after {} minutes\n".format(values.tool_name, text, time_total))
    else:
        error("Could not process configuration arguments\n")


def emit_help() -> None:
    benchmarks = random.sample(
        list(filter(lambda x: x != "examples", values.get_list_benchmarks())), 3
    )
    tools = random.sample(values.get_list_tools(), 3)
    max_length = len(definitions.ARG_BUG_INDEX_LIST)  # hardcoded

    write(
        f"Usage: cerberus [OPTIONS] --benchmark={'/'.join(benchmarks)}... --tool={'/'.join(tools)}... ",
        COLOR.WHITE,
    )
    write("Options are:", COLOR.WHITE)
    write(
        "\t"
        + definitions.ARG_DATA_PATH.ljust(max_length)
        + "\t| "
        + "directory for experiments",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_NAME.ljust(max_length)
        + "\t| "
        + "name of the tool ({})".format(",".join(tools)),
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BENCHMARK.ljust(max_length)
        + "\t| "
        + "name of the benchmark ({})".format(",".join(benchmarks)),
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_PATH.ljust(max_length)
        + "\t| "
        + "path of the tool",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_PARAMS.ljust(max_length)
        + "\t| "
        + "parameters for the tool",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_DEBUG_MODE.ljust(max_length)
        + "\t| "
        + "enable debug mode",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_INSTRUMENT_ONLY.ljust(max_length)
        + "\t| "
        + "only instrument the project",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_SETUP_ONLY.ljust(max_length)
        + "\t| "
        + "only setup the project",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BUG_INDEX.ljust(max_length)
        + "\t| "
        + "run only the specified experiment",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BUG_INDEX_LIST.ljust(max_length)
        + "\t| "
        + "runs a list of experiments",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_START_INDEX.ljust(max_length)
        + "\t| "
        + "specify a range of experiments starting from ID",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_END_INDEX.ljust(max_length)
        + "\t| "
        + "specify a range of experiments that ends at ID",
        COLOR.WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TASK_PROFILE_ID_LIST.ljust(max_length)
        + "\t| "
        + "specify a different profile using config ID",
        COLOR.WHITE,
    )
