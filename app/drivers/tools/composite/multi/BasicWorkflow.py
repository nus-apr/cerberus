import os
from os.path import join

from app.core import configuration
from app.core import definitions
from app.core import values
from app.core.main import create_task_identifier
from app.core.main import create_task_image_identifier
from app.core.task import analyze
from app.core.task import fuzz
from app.core.task import repair
from app.core.task import select
from app.core.task import task
from app.core.task.typing.CompositeSequence import CompositeSequence
from app.core.task.typing.DirectoryInfo import DirectoryInfo
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.composite.AbstractCompositeTool import AbstractCompositeTool


class BasicWorkflow(AbstractCompositeTool):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bindings = {
            values.dir_dynamic: {
                "bind": "/dynamic-link",
                "mode": "rw",
            }
        }
        super().__init__(self.name)
        # preferably change to a container with the dependencies ready to reduce setup time
        self.image_name = "ubuntu:20.04"

    def run_composite(
        self,
        dir_info: DirectoryInfo,
        benchmark: AbstractBenchmark,
        bug_info,
        composite_config_info,
        container_config_info,
        run_index,
    ):
        super(BasicWorkflow, self).run_composite(
            dir_info,
            benchmark,
            bug_info,
            composite_config_info,
            container_config_info,
            run_index,
        )
        """
            self.dir_logs - directory to store logs
            self.dir_setup - directory to access setup scripts
            self.dir_expr - directory for experiment
            self.dir_output - directory to store artifacts/output
        """

        self.emit_debug(composite_config_info)
        composite_sequence = composite_config_info[self.key_composite_sequence]
        tool_tag = composite_config_info.get(definitions.KEY_TOOL_TAG, "")

        self.emit_normal("setting up workflow")
        self.emit_debug(composite_sequence)
        for task_type, tools in composite_sequence.items():
            for tool_name in tools:
                tool = configuration.load_tool(tool_name, task_type)
                tool.check_tool_exists()
                image_name = create_task_image_identifier(
                    benchmark,
                    tool,
                    bug_info,
                    tool_tag,
                )
                experiment_image_id = task.prepare_experiment(
                    benchmark,
                    bug_info,
                    composite_config_info[self.key_cpus],
                    [],
                    tool_tag,
                )
                task.prepare_experiment_tool(
                    experiment_image_id, tool, dir_info, image_name, tool_tag
                )
                key = create_task_identifier(
                    benchmark,
                    composite_config_info,
                    container_config_info,
                    bug_info,
                    tool,
                    str(run_index),
                    tool_tag,
                )

                # task.run(
                #    benchmark,
                #    tool,
                #    bug_info,
                #    composite_config_info,
                #    container_config_info,
                #    key,
                #    composite_config_info[self.key_cpus],
                #    composite_config_info[self.key_gpus],
                #    image_name,
                # )
        self.emit_highlight("Done with setup!")
        input()
        pass

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
