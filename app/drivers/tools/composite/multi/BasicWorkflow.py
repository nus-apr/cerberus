import os
from os.path import join

from app.core import definitions
from app.core.task import analyze
from app.core.task import fuzz
from app.core.task import repair
from app.core.task import select
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.tools.composite.AbstractCompositeTool import AbstractCompositeTool


class BasicWorkflow(AbstractCompositeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super().__init__(self.name)
        self.image_name = "ubuntu:20.04"

    def setup_workflow(self, composite_sequence: CompositeSequence):
        self.emit_debug("setting up workflow")
        self.emit_debug(composite_sequence)
        pass

    def run_composite(self, dir_info: DirectoryInfo, bug_info, composite_config_info):
        super(BasicWorkflow, self).run_composite(
            dir_info, bug_info, composite_config_info
        )
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        timeout_h = str(composite_config_info[self.key_timeout])
        # start running
        self.timestamp_log_start()

        self.timestamp_log_end()
        self.emit_highlight("log file: {0}".format(self.log_output_path))

    def save_artifacts(self, dir_info):
        """
        Save useful artifacts from the repair execution
        output folder -> self.dir_output
        logs folder -> self.dir_logs
        The parent method should be invoked at last to archive the results
        """
        super().save_artifacts(dir_info)

    def analyse_output(self, dir_info, bug_id, fail_list):
        self.emit_normal("reading output")

        return self.stats
