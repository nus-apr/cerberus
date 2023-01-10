import os
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.core import definitions, emitter


class Examples(AbstractBenchmark):
    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        self.bench_dir_path = os.path.abspath(
            os.path.dirname(__file__) + "/../../benchmark/"
        )
        self.setup_dir_path = self.bench_dir_path
        super(Examples, self).__init__()

    def setup(self, tool_name, bug_index, config_id, test_all, use_container, is_multi):
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        tool_name_dir = tool_name
        if is_multi:
            tool_name_dir = "multi"
        self.log_dir_path = (
            definitions.DIR_LOGS
            + "/"
            + str(config_id)
            + "-"
            + self.name
            + "-"
            + tool_name_dir
            + "-"
            + subject_name
            + "-"
            + bug_id
        )
        container_id = self.setup_container(
            tool_name, bug_index, config_id, use_container, is_multi
        )
        exp_setup_dir_path = (
            self.setup_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
        )
        if not use_container:
            self.base_dir_experiment = os.path.abspath(
                os.path.dirname(__file__) + "/../../experiments/"
            )
            dir_exp_local = (
                definitions.DIR_EXPERIMENT
                + "/"
                + self.name
                + "/"
                + subject_name
                + "/"
                + bug_id
            )
            if os.path.isdir(dir_exp_local):
                os.system("rm -rf {}".format(dir_exp_local))
        self.setup_experiment(
            exp_setup_dir_path, bug_index, config_id, container_id, test_all, tool_name
        )
        return container_id

    def deploy(self, setup_dir_path, bug_id, config_id, container_id, tool_name):
        emitter.normal("\t\t\tsetting up experiment subject")
        self.log_deploy_path = (
            self.log_dir_path
            + "/"
            + tool_name
            + "-"
            + self.name
            + "-"
            + bug_id
            + "-deploy.log"
        )
        command_str = "bash setup.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            command_str, self.log_deploy_path, setup_dir_path, container_id
        )
        return status == 0

    def config(self, setup_dir_path, bug_id, config_id, container_id, tool_name):
        return True

    def build(self, setup_dir_path, bug_id, config_id, container_id, tool_name):
        emitter.normal("\t\t\tbuilding experiment subject")
        self.log_build_path = (
            self.log_dir_path
            + "/"
            + tool_name
            + "-"
            + self.name
            + "-"
            + bug_id
            + "-build.log"
        )
        command_str = "bash build.sh {}".format(self.base_dir_experiment)
        status = self.run_command(
            command_str, self.log_build_path, setup_dir_path, container_id
        )
        return status == 0

    def test(self, setup_dir_path, bug_id, config_id, container_id, tool_name):
        return True

    def test_all(
        self, setup_dir_path, experiment_item, config_id, container_id, tool_name
    ):
        return True

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(command_str, "/dev/null", "/", container_id)
        return

    def save_artefacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artefacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Examples, self).save_artefacts(dir_info, container_id)
