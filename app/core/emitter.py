# -*- coding: utf-8 -*-

import os
import sys
import textwrap

from app.core import definitions, values, logger

rows, columns = tuple(map(int, os.popen("stty size", "r").read().split()))
GREY = "\t\x1b[1;30m"
RED = "\t\x1b[1;31m"
GREEN = "\x1b[1;32m"
YELLOW = "\t\x1b[1;33m"
BLUE = "\t\x1b[1;34m"
ROSE = "\t\x1b[1;35m"
CYAN = "\x1b[1;36m"
WHITE = "\t\x1b[1;37m"

PROG_OUTPUT_COLOR = "\t\x1b[0;30;47m"
STAT_COLOR = "\t\x1b[0;32;47m"


def write(print_message, print_color, new_line=True, prefix=None, indent_level=0):
    message = "\033[K{}{}\x1b[0m".format(print_color, print_message)
    if prefix:
        prefix = "\033[K{}{}\x1b[0m".format(print_color, prefix)
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


def title(title):
    write("\n" + "=" * 100 + "\n\n\t" + title + "\n" + "=" * 100 + "\n", CYAN)
    logger.information(title)


def sub_title(text):
    write("\n\t" + text + "\n\t" + "_" * 90 + "\n", CYAN)
    logger.information(text)


def sub_sub_title(text):
    write("\n\t\t" + text + "\n\t\t" + "_" * 90 + "\n", CYAN)
    logger.information(text)


def command(message):
    if values.debug:
        prefix = "\t\t[command] "
        write(message, ROSE, prefix=prefix, indent_level=2)
    logger.command(message)


def docker_command(message):
    if values.debug:
        prefix = "\t\t[docker-command] "
        write(message, ROSE, prefix=prefix, indent_level=2)
    logger.docker_command(message)


def debug(message):
    if values.debug:
        prefix = "\t\t[debug] "
        write(message, GREY, prefix=prefix, indent_level=2)
    logger.debug(message)

def build(message):
    if values.debug:
        prefix = "\t\t[build] "
        write(message, GREY, prefix=prefix, indent_level=2)
    logger.build(message)

def data(message, info=None):
    if values.debug:
        prefix = "\t\t[data] "
        write(message, GREY, prefix=prefix, indent_level=2)
        if info:
            write(info, GREY, prefix=prefix, indent_level=2)
    logger.data(message, info)


def normal(message, jump_line=True):
    write(message, BLUE, jump_line)
    logger.output(message)


def highlight(message, jump_line=True):
    indent_length = message.count("\t")
    prefix = "\t" * indent_length
    message = message.replace("\t", "")
    write(message, WHITE, jump_line, indent_level=indent_length, prefix=prefix)
    logger.note(message)


def information(message, jump_line=True):
    write(message, GREY, jump_line)
    logger.information(message)


def statistics(message):
    write(message, WHITE)
    logger.output(message)


def error(message):
    write(message, RED)
    logger.error(message)


def success(message):
    write(message, GREEN)
    logger.output(message)


def special(message):
    write(message, ROSE)
    logger.note(message)


def program_output(output_message):
    write("\t\tProgram Output:", WHITE)
    if type(output_message) == list:
        for line in output_message:
            write("\t\t\t" + line.strip(), PROG_OUTPUT_COLOR)
    else:
        write("\t\t\t" + output_message, PROG_OUTPUT_COLOR)


def emit_patch(patch_lines, jump_line=True, message=""):
    output = message
    indent_length = 2
    prefix = "\t\t" * indent_length
    for line in patch_lines:
        write(line, ROSE, jump_line, indent_level=indent_length, prefix=prefix)


def warning(message):
    write(message, YELLOW)
    logger.warning(message)


def note(message):
    write(message, WHITE)
    logger.note(message)


def configuration(setting, value):
    message = "\t[config] " + setting + ": " + str(value)
    write(message, WHITE, True)
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


def emit_help():
    benchmarks = list(filter(lambda x: x != "examples", os.listdir("./benchmark/")))[:3]
    tools = [x.replace(".py", "") for x in os.listdir(values.dir_tool_drivers)
             if ".py" in x and "__" not in x][:3]
    max_length = len(definitions.ARG_BUG_INDEX_LIST)  # hardcoded

    write(
        f"Usage: cerberus [OPTIONS] --benchmark={'/'.join(benchmarks[0:3])}... --tool={'/'.join(tools[0:3])}... ",
        WHITE,
    )
    write("Options are:", WHITE)
    write(
        "\t"
        + definitions.ARG_DATA_PATH.ljust(max_length)
        + "\t| "
        + "directory for experiments",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_NAME.ljust(max_length)
        + "\t| "
        + "name of the tool ({})".format(",".join(tools)),
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BENCHMARK.ljust(max_length)
        + "\t| "
        + "name of the benchmark ({})".format(",".join(benchmarks)),
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_PATH.ljust(max_length)
        + "\t| "
        + "path of the tool",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_TOOL_PARAMS.ljust(max_length)
        + "\t| "
        + "parameters for the tool",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_DEBUG_MODE.ljust(max_length)
        + "\t| "
        + "enable debug mode",
        WHITE,
    )    
    write(
        "\t"
        + definitions.ARG_INSTRUMENT_ONLY.ljust(max_length)
        + "\t| "
        + "only instrument the project",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_SETUP_ONLY.ljust(max_length)
        + "\t| "
        + "only setup the project",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BUG_INDEX.ljust(max_length)
        + "\t| "
        + "run only the specified experiment",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_BUG_INDEX_LIST.ljust(max_length)
        + "\t| "
        + "runs a list of experiments",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_START_INDEX.ljust(max_length)
        + "\t| "
        + "specify a range of experiments starting from ID",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_END_INDEX.ljust(max_length)
        + "\t| "
        + "specify a range of experiments that ends at ID",
        WHITE,
    )
    write(
        "\t"
        + definitions.ARG_CONFIG_ID_LIST.ljust(max_length)
        + "\t| "
        + "specify a different profile using config ID",
        WHITE,
    )
