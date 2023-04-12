import os
from os.path import join

from app.core import definitions
from app.core import emitter
from app.core import values
from app.core.task.status import TaskStatus
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark


class Vul4J(AbstractBenchmark):

    log_instrument_path = None

    def __init__(self):
        self.name = os.path.basename(__file__)[:-3].lower()
        super(Vul4J, self).__init__()

    def setup_container(self, bug_index, image_name, cpu: str):
        """
        Setup the container for the experiment by constructing volumes,
        which point to certain folders in the project
        """

        container_id = super(Vul4J, self).setup_container(bug_index, image_name, cpu)
        return container_id

    def setup_experiment(self, bug_index, container_id, test_all):
        is_error = super(Vul4J, self).setup_experiment(
            bug_index, container_id, test_all
        )

        if self.compress_dependencies(container_id, bug_index):
            emitter.success("\t\t\t(benchmark) dependencies compressed successfully")
        else:
            emitter.error("\t\t\t(benchmark) dependencies compressed failed")
            is_error = True

        return is_error

    def deploy(self, bug_index, container_id):
        emitter.normal("\t\t\tdownloading experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        vul4j_id = str(experiment_item["vul4j_id"])

        # get project from the branch
        github_repo_url = "https://github.com/nus-apr/vul4j.git"
        command_str = "git clone --single-branch --branch {0} {1} {2}".format(
            vul4j_id,
            github_repo_url,
            join(self.dir_expr, "src"),
        )
        status = self.run_command(container_id, command_str, self.log_deploy_path)

        return status == 0

    def config(self, bug_index, container_id):
        emitter.normal("\t\t\tconfiguring experiment subject")
        return True

    def build(self, bug_index, container_id):
        emitter.normal("\t\t\tbuilding experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]

        timeout_h = 1
        set_java_home_cmd = "JAVA_HOME=$JAVA{0}_HOME".format(
            experiment_item[definitions.KEY_JAVA_VERSION]
        )

        command_str = "bash -c '{0} timeout -k 5m {1}h {2}'".format(
            set_java_home_cmd, timeout_h, experiment_item[definitions.KEY_COMPILE_CMD]
        )
        status = self.run_command(
            container_id, command_str, self.log_build_path, join(self.dir_expr, "src")
        )

        if status != 0:
            command_str = "bash -c 'timeout -k 5m {0}h {1}'".format(
                timeout_h, experiment_item[definitions.KEY_COMPILE_CMD]
            )
            status = self.run_command(
                container_id,
                command_str,
                self.log_build_path,
                join(self.dir_expr, "src"),
            )

        return status == 0

    def compress_dependencies(self, container_id, bug_index):
        emitter.normal("\t\t\tcompress experiment subject's dependencies")
        experiment_item = self.experiment_subjects[bug_index - 1]
        build_system = experiment_item[definitions.KEY_BUILD_SYSTEM]
        set_java_home_cmd = "JAVA_HOME=$JAVA{0}_HOME".format(
            experiment_item[definitions.KEY_JAVA_VERSION]
        )

        if build_system != "maven":
            return True

        command_str = "bash -c '{0} mvn dependency:copy-dependencies'".format(
            set_java_home_cmd
        )
        status = self.run_command(
            container_id,
            command_str,
            self.log_build_path,
            join(
                self.dir_expr,
                "src",
                experiment_item[definitions.KEY_FAILING_MODULE_DIRECTORY],
            ),
        )

        if status != 0:
            command_str = "bash -c 'mvn dependency:copy-dependencies'"
            status = self.run_command(
                container_id,
                command_str,
                self.log_build_path,
                join(
                    self.dir_expr,
                    "src",
                    experiment_item[definitions.KEY_FAILING_MODULE_DIRECTORY],
                ),
            )

            if status != 0:
                return False

        command_str = "bash -c '{0} {1}'".format(
            join(self.dir_expr, "base", "init_dependencies.sh"),
            join(
                self.dir_expr,
                "src",
                experiment_item[definitions.KEY_FAILING_MODULE_DIRECTORY],
                "target",
            ),
        )
        status = self.run_command(container_id, command_str, self.log_build_path)

        return status == 0

    def test(self, bug_index, container_id):
        emitter.normal("\t\t\ttesting experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]

        set_java_home_cmd = "JAVA_HOME=$JAVA{0}_HOME".format(
            experiment_item[definitions.KEY_JAVA_VERSION]
        )
        command_str = "bash -c '{0} {1}'".format(
            set_java_home_cmd, experiment_item[definitions.KEY_TEST_ALL_CMD]
        )
        status = self.run_command(
            container_id, command_str, self.log_test_path, join(self.dir_expr, "src")
        )

        if status != 0:
            command_str = "bash -c '{0}'".format(
                experiment_item[definitions.KEY_TEST_ALL_CMD]
            )
            status = self.run_command(
                container_id,
                command_str,
                self.log_test_path,
                join(self.dir_expr, "src"),
            )

        return status == 0

    def clean(self, exp_dir_path, container_id):
        emitter.normal("\t\t\tremoving experiment subject")
        command_str = "rm -rf " + exp_dir_path
        self.run_command(container_id, command_str)
        return

    def save_artifacts(self, dir_info, container_id):
        emitter.normal("\t\t[benchmark] saving experiment artifacts")
        self.list_artifact_dirs = []  # path should be relative to experiment directory
        self.list_artifact_files = []  # path should be relative to experiment directory
        super(Vul4J, self).save_artifacts(dir_info, container_id)
