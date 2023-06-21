import logging
import os
import textwrap
import time
from enum import Enum
from os.path import join

import rich

from app.core.configs.Config import Config
from app.core.configs.general.GeneralConfig import GeneralConfig
from app.core.dirs.BaseDirsInfo import BaseDirsInfo


class Emitter:
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

    def __init__(self,
                 general_config: GeneralConfig,
                 base_dirs_info: BaseDirsInfo
                 ):

        self.general_config = general_config

        dir_log_base = base_dirs_info.get_log_base_dir()
        self._logger_main = self.setup_logger("main", join(dir_log_base, "log-" + str(time.time())), level=logging.DEBUG)
        self._logger_error = self.setup_logger("error", join(dir_log_base, "log-error"))
        self._logger_command = self.setup_logger("command", join(dir_log_base, "log-command"))
        self._logger_build = self.setup_logger("build", join(dir_log_base, "log-build"))

        stty_info = os.popen("stty size", "r")
        self.rows, self.columns = tuple(map(int, stty_info.read().split()))
        stty_info.close()

    @staticmethod
    def setup_logger(name, log_file, level=logging.INFO, formatter=None):
        """To setup as many loggers as you want"""
        if formatter is None:
            formatter = logging.Formatter("%(asctime)s m%(levelname)s %(message)s")
        handler = logging.FileHandler(log_file, mode="w")
        handler.setFormatter(formatter)
        logger = logging.getLogger(name)
        logger.setLevel(level)
        logger.addHandler(handler)
        return logger

    # write to stdout or ui window
    def write(self, print_message, print_color, new_line=True, prefix=None, indent_level=0):
        if not self.general_config.is_ui_mode():
            message = "[bold {}]{}".format(
                self.RICH_COLOR_MAP[print_color], str(print_message).replace("[", "\\[")
            )
            if prefix:
                prefix = "[{}]{}".format(self.RICH_COLOR_MAP[print_color], prefix)
                len_prefix = ((indent_level + 1) * 4) + len(prefix)
                wrapper = textwrap.TextWrapper(
                    initial_indent=prefix,
                    subsequent_indent=" " * len_prefix,
                    width=int(self.columns),
                )
                message = wrapper.fill(message)
            rich.print(message, end=("\n" if new_line else "\r"))
        else:
            if prefix:
                print_message = prefix + str(print_message)

            # ui.post_write(
            #     "[bold {}]{} {}".format(
            #         self.TEXTUALIZE_COLOR_MAP[print_color],
            #         # values.job_identifier.get("Root"),
            #         str(print_message).replace("[", "\\["),
            #     )
            # )

    def normal(self, message, jump_line=True):
        self.write(message, self.COLOR.BLUE, jump_line)
        message = "[OUTPUT]: {}".format(str(message).strip())
        self._logger_main.info(message)

    def highlight(self, message, jump_line=True):
        indent_length = message.count("\t")
        prefix = "\t" * indent_length
        message = message.replace("\t", "")
        self.write(message, self.COLOR.WHITE, jump_line, indent_level=indent_length, prefix=prefix)
        self._logger_main.info(message)

    def information(self, message, jump_line=True):
        self.write(message, self.COLOR.GREY, jump_line)
        self._logger_main.info(message)

    def debug(self, message, is_debug=False):
        if is_debug:
            prefix = "\t\t(debug) "
            self.write(message, self.COLOR.GREY, prefix=prefix, indent_level=2)
        self._logger_main.debug(str(message).strip())

    def error(self, message):
        self.write(message, self.COLOR.RED)
        self._logger_main.error(message)
        self._logger_error.error(message)

    def warning(self, message):
        self.write(message, self.COLOR.YELLOW)
        message = str(message).strip().lower().replace("[warning]", "")
        self._logger_main.warning(message)

    def note(self, message):
        self.write(message, self.COLOR.WHITE)
        self._logger_main.info(message)

    def success(self, message):
        self.write(message, self.COLOR.GREEN)
        message = "[OUTPUT]: {}".format(str(message).strip())
        self._logger_main.info(message)

    def special(self, message):
        self.write(message, self.COLOR.ROSE)
        self._logger_main.info(message)

    # pre-defined formats
    def title(self, title):
        self.write("\n" + "=" * 100 + "\n\n\t" + title + "\n" + "=" * 100 + "\n", self.COLOR.CYAN)
        self._logger_main.info(title)

    def sub_title(self, text):
        self.write("\n\t" + text + "\n\t" + "_" * 90 + "\n", self.COLOR.CYAN)
        self._logger_main.info(text)

    def sub_sub_title(self, text):
        self.write("\n\t\t" + text + "\n\t\t" + "_" * 90 + "\n", self.COLOR.CYAN)
        self._logger_main.info(text)

    def command(self, message, is_debug=False):
        if is_debug:
            prefix = "\t\t[command] "
            self.write(message, self.COLOR.ROSE, prefix=prefix, indent_level=2)
        message = str(message).strip().replace("[command]", "")
        message = "[COMMAND]: {}\n".format(message)
        self._logger_main.info(message)
        self._logger_command.info(message)

    def docker_command(self, message, is_debug=False):
        if is_debug:
            prefix = "\t\t[docker-command] "
            self.write(message, self.COLOR.ROSE, prefix=prefix, indent_level=2)
        message = str(message).strip().replace("[command]", "")
        message = "[DOCKER-COMMAND]: {}\n".format(message)
        self._logger_main.info(message)
        self._logger_command.info(message)

    def build(self, message, is_debug=False):
        if is_debug:
            prefix = "\t\t[build] "
            self.write(message, self.COLOR.GREY, prefix=prefix, indent_level=2)
        self._logger_build.info(message)

    # not used
    def data(self, message, info=None, is_debug=False):
        if is_debug:
            prefix = "\t\t[data] "
            self.write(message, self.COLOR.GREY, prefix=prefix, indent_level=2)
            if info:
                self.write(info, self.COLOR.GREY, prefix=prefix, indent_level=2)
        self._logger_main.info(message, info)

    def configuration(self, config):
        for setting, value in config.__dict__.items():
            message = "\t[config] " + setting + ": " + str(value)
            self.write(message, self.COLOR.WHITE, True)
            message = str(setting + ":" + str(value)).strip().lower().replace("[config]", "")
            message = "[CONFIGURATION]: {}\n".format(message)
            self._logger_main.info(message)

    def statistics(self, message):
        self.write(message, self.COLOR.WHITE)
        message = str(message).strip()
        message = "[OUTPUT]: {}".format(message)
        self._logger_main.info(message)

    # TODO review
    # def end(self, time_total, is_error=False):
    #     if values.arg_pass:
    #         self.statistics("\nRun time statistics:\n-----------------------\n")
    #         self.statistics("Experiment Count: " + str(values.iteration_no))
    #         if is_error:
    #             self.error(
    #                 "\n"
    #                 + values.tool_name
    #                 + " exited with an error after "
    #                 + time_total
    #                 + " minutes \n"
    #             )
    #         else:
    #             self.success(
    #                 "\n"
    #                 + values.tool_name
    #                 + " finished successfully after "
    #                 + time_total
    #                 + " minutes \n"
    #             )
    #     else:
    #         self.error("Could not process configuration arguments\n")
