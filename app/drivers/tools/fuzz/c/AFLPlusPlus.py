import os
from os.path import join

from app.drivers.tools.fuzz.AbstractFuzzTool import AbstractFuzzTool


class AFLPlusPlus(AbstractFuzzTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "mirchevmp/aflplusplus"

    def analyse_output(self, dir_info, bug_id, fail_list):
        """
        analyse tool output and collect information
        output of the tool is logged at self.log_output_path
        information required to be extracted are:
        """
        return self.stats

    def run_fuzz(self, bug_info, fuzz_config_info):
        super(AFLPlusPlus, self).run_fuzz(bug_info, fuzz_config_info)
        self.emit_normal("executing fuzz command")

        timeout = int(float(fuzz_config_info[self.key_timeout]) * 60)

        if self.key_bin_path not in bug_info:
            self.error_exit("no binary path provided")

        self.timestamp_log_start()

        initial_corpus = join(self.dir_setup, self.name, "initial-corpus")

        dictionary = ""
        if self.is_file(join(self.dir_setup, self.name, "autodict.dict")):
            dictionary = "-x {}".format(
                join(self.dir_setup, self.name, "autodict.dict")
            )

        self.run_command("mkdir {}".format(initial_corpus))

        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, "benign_tests"),
                initial_corpus,
            )
        )
        self.run_command(
            "bash -c 'cp -r {}/* {}' ".format(
                join(self.dir_setup, "crashing_tests"),
                initial_corpus,
            )
        )

        fuzz_command = "bash -c 'stty cols 100 && stty rows 100 && timeout -k 5m {timeout}m afl-fuzz -i {input_folder} -o {output_folder} -d -m none {dict} {additional_params} -- {binary} {binary_input}'".format(
            timeout=timeout,
            additional_params=bug_info.get(self.key_tool_params, ""),
            input_folder=initial_corpus,
            output_folder=self.dir_output,
            dict=dictionary,
            binary=join(self.dir_expr, "src", bug_info[self.key_bin_path]),
            binary_input=bug_info[self.key_crash_cmd].replace("$POC", "@@"),
        )

        status = self.run_command(
            fuzz_command, self.log_output_path, join(self.dir_expr, "src")
        )

        self.process_status(status)

        self.timestamp_log_end()
