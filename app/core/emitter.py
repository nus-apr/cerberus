# -*- coding: utf-8 -*-
import os
import random
import sys
import textwrap
from enum import Enum

from textual.widgets import TextLog

from app.core import definitions
from app.core import logger
from app.core import ui
from app.core import values

rows, columns = tuple(map(int, os.popen("stty size", "r").read().split()))


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


TERMINAL_COLOR_MAP = {
    COLOR.GREY: "\t\x1b[1;30m",
    COLOR.RED: "\t\x1b[1;31m",
    COLOR.GREEN: "\x1b[1;32m",
    COLOR.YELLOW: "\t\x1b[1;33m",
    COLOR.BLUE: "\t\x1b[1;34m",
    COLOR.ROSE: "\t\x1b[1;35m",
    COLOR.CYAN: "\x1b[1;36m",
    COLOR.WHITE: "\t\x1b[1;37m",
    COLOR.PROG_OUTPUT_COLOR: "\t\x1b[0;30;47m",
    COLOR.STAT_COLOR: "\t\x1b[0;32;47m",
}

TEXTUALIZE_COLOR_MAP = {
    COLOR.GREY: "grey",
    COLOR.RED: "red",
    COLOR.GREEN: "green",
    COLOR.YELLOW: "yellow",
    COLOR.BLUE: "blue",
    COLOR.ROSE: "pink",
    COLOR.CYAN: "cyan",
    COLOR.WHITE: "white",
    COLOR.PROG_OUTPUT_COLOR: "green",
    COLOR.STAT_COLOR: "green",
}


def write(print_message, print_color, new_line=True, prefix=None, indent_level=0):
    message = "\033[K{}{}\x1b[0m".format(TERMINAL_COLOR_MAP[print_color], print_message)
    if not values.ui_active:
        if prefix:
            prefix = "\033[K{}{}\x1b[0m".format(TERMINAL_COLOR_MAP[print_color], prefix)
            len_prefix = ((indent_level + 1) * 4) + len(prefix)
            wrapper = textwrap.TextWrapper(
                initial_indent=prefix,
                subsequent_indent=" " * len_prefix,
                width=int(columns),
            )
            message = wrapper.fill(message)
        sys.stdout.write(message)
        sys.stdout.write("\n" if new_line else "\033[K\r")
        sys.stdout.flush()
    else:
        if prefix:
            print_message = prefix + print_message
        ui.get_ui().post_message_no_wait(
            ui.Write(
                sender=ui.get_ui(),
                text="[bold {}]{}".format(
                    TEXTUALIZE_COLOR_MAP[print_color], print_message
                ),
            )
        )


def title(title):
    write("\n" + "=" * 100 + "\n\n\t" + title + "\n" + "=" * 100 + "\n", COLOR.CYAN)
    logger.information(title)


def sub_title(text):
    write("\n\t" + text + "\n\t" + "_" * 90 + "\n", COLOR.CYAN)
    logger.information(text)


def sub_sub_title(text):
    write("\n\t\t" + text + "\n\t\t" + "_" * 90 + "\n", COLOR.CYAN)
    logger.information(text)


def command(message):
    if values.debug:
        prefix = "\t\t(command) "
        write(message, COLOR.ROSE, prefix=prefix, indent_level=2)
    logger.command(message)


def docker_command(message):
    if values.debug:
        prefix = "\t\t(docker-command) "
        write(message, COLOR.ROSE, prefix=prefix, indent_level=2)
    logger.docker_command(message)


def debug(message):
    if values.debug:
        prefix = "\t\t(debug) "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.debug(message)


def build(message):
    if values.debug:
        prefix = "\t\t(build) "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.build(message)


def data(message, info=None):
    if values.debug:
        prefix = "\t\t(data) "
        write(message, COLOR.GREY, prefix=prefix, indent_level=2)
        if info:
            write(info, COLOR.GREY, prefix=prefix, indent_level=2)
    logger.data(message, info)


def normal(message, jump_line=True):
    write(message, COLOR.BLUE, jump_line)
    logger.output(message)


def highlight(message, jump_line=True):
    indent_length = message.count("\t")
    prefix = "\t" * indent_length
    message = message.replace("\t", "")
    write(message, COLOR.WHITE, jump_line, indent_level=indent_length, prefix=prefix)
    logger.note(message)


def information(message, jump_line=True):
    write(message, COLOR.GREY, jump_line)
    logger.information(message)


def statistics(message):
    write(message, COLOR.WHITE)
    logger.output(message)


def error(message):
    write(message, COLOR.RED)
    logger.error(message)


def success(message):
    write(message, COLOR.GREEN)
    logger.output(message)


def special(message):
    write(message, COLOR.ROSE)
    logger.note(message)


def program_output(output_message):
    write("\t\tProgram Output:", COLOR.WHITE)
    if type(output_message) == list:
        for line in output_message:
            write("\t\t\t" + line.strip(), COLOR.PROG_OUTPUT_COLOR)
    else:
        write("\t\t\t" + output_message, COLOR.PROG_OUTPUT_COLOR)


def emit_patch(patch_lines, jump_line=True, message=""):
    output = message
    indent_length = 2
    prefix = "\t\t" * indent_length
    for line in patch_lines:
        write(line, COLOR.ROSE, jump_line, indent_level=indent_length, prefix=prefix)


def warning(message):
    write(message, COLOR.YELLOW)
    logger.warning(message)


def note(message):
    write(message, COLOR.WHITE)
    logger.note(message)


def configuration(setting, value):
    message = "\t(config) " + setting + ": " + str(value)
    write(message, COLOR.WHITE, True)
    logger.configuration(setting + ":" + str(value))


def end(time_total, is_error=False):
    if values.arg_pass:
        statistics("\nRun time statistics:\n-----------------------\n")
        statistics("Experiment Count: " + str(values.iteration_no))
        if is_error:
            error(
                "\n"
                + values.tool_name
                + " exited with an error after "
                + time_total
                + " minutes \n"
            )
        else:
            success(
                "\n"
                + values.tool_name
                + " finished successfully after "
                + time_total
                + " minutes \n"
            )
    else:
        error("Could not process configuration arguments\n")


def emit_help():
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
        + definitions.ARG_PROFILE_ID_LIST.ljust(max_length)
        + "\t| "
        + "specify a different profile using config ID",
        COLOR.WHITE,
    )
