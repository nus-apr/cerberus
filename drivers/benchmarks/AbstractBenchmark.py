import abc
import os
import json
import shutil
from os.path import join
from app import emitter, utilities, container, definitions, abstractions, values


class AbstractBenchmark:
    experiment_subjects = []
    meta_file = None
    bench_dir_path = None
    name = None
    image_name = None
    __dir_info = None
    dir_logs = ""
    dir_expr = ""
    dir_base_expr = ""
    dir_inst = ""
    dir_setup = ""
    log_dir_path = "None"
    log_deploy_path = "None"
    log_config_path = "None"
    log_build_path = "None"
    log_test_path = "None"
    size = 0
    list_artifact_dirs = []
    list_artifact_files = []
    base_dir_experiment = "/experiment/"

    def __init__(self):
        self.bench_dir_path = os.path.abspath(
            os.path.dirname(__file__) + "/../../benchmark/"
        )
        self.meta_file = self.bench_dir_path + "/" + self.name + "/meta-data.json"
        self.image_name = "{}-benchmark".format(self.name)
        if values.DEFAULT_USE_CONTAINER:
            self.build_benchmark_image()
        self.load()

    def read_file(self, container_id, file_path, encoding="utf-8"):
        return abstractions.read_file(container_id, file_path, encoding)

    def append_file(self, container_id, content, file_path):
        return abstractions.append_file(container_id, content, file_path)

    def update_dir_info(self, dir_info):
        self.__dir_info = dir_info
        if not values.DEFAULT_USE_CONTAINER:
            self.dir_expr = dir_info["local"]["experiment"]
            self.dir_logs = dir_info["local"]["logs"]
            self.dir_setup = dir_info["local"]["setup"]
            self.dir_base_expr = definitions.DIR_EXPERIMENT
        else:
            self.dir_expr = dir_info["container"]["experiment"]
            self.dir_logs = dir_info["container"]["logs"]
            self.dir_setup = dir_info["container"]["setup"]
            self.dir_base_expr = "/experiment/"

    def get_list(self):
        return self.experiment_subjects

    def load(self):
        emitter.normal("loading experiment meta-data")
        if os.path.isfile(self.meta_file):
            with open(self.meta_file, "r") as in_file:
                json_data = json.load(in_file)
                if json_data:
                    self.experiment_subjects = json_data
                    self.size = len(json_data)
                else:
                    utilities.error_exit(
                        "could not load meta-data from ", self.meta_file
                    )
        else:
            utilities.error_exit("Meta file does not exist")
        return

    def run_command(
        self,
        container_id,
        command_str,
        log_file_path="/dev/null",
        dir_path="/experiment",
    ):
        if container_id:
            exit_code, output = container.exec_command(
                container_id, command_str, dir_path
            )
            stdout, stderr = output
            if "/dev/null" not in log_file_path:
                if stdout:
                    self.append_file(
                        container_id, stdout.decode("iso-8859-1"), log_file_path
                    )
                if stderr:
                    self.append_file(
                        container_id, stderr.decode("iso-8859-1"), log_file_path
                    )
        else:
            command_str = "cd " + dir_path + ";" + command_str
            command_str += " > {0} 2>&1".format(log_file_path)
            exit_code = utilities.execute_command(command_str)
        return exit_code

    def build_benchmark_image(self):
        if not container.is_image_exist(self.image_name):
            emitter.warning("\t[benchmark] benchmark environment not found")
            emitter.normal("\t[benchmark] building benchmark environment")
            container.build_benchmark_image(self.image_name)
        else:
            emitter.success("\t\tpre-built benchmark environment found")

    def build_experiment_image(self, bug_index, test_all, exp_image_name):
        container_id = self.setup_container(bug_index, self.image_name)
        is_error = self.setup_experiment(bug_index, container_id, test_all)
        if is_error:
            utilities.error_exit("setting up experiment failed")
        container_obj = container.get_container(container_id)
        container_obj.commit(exp_image_name)

    def setup_container(self, bug_index, image_name):
        container_id = None
        emitter.normal("\t\t[benchmark] preparing experiment environment")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        dir_exp_local = join(
            definitions.DIR_EXPERIMENT, self.name, subject_name, bug_id
        )

        if os.path.isdir(dir_exp_local):
            shutil.rmtree(dir_exp_local)

        volume_list = {
            self.__dir_info["local"]["setup"]: {"bind": "/scripts", "mode": "rw"},
            os.path.join(self.__dir_info["local"]["setup"], "../../app", "base"): {
                "bind": join(
                    "/experiments", "benchmark", self.name, subject_name, "base"
                ),
                "mode": "rw",
            },
            os.path.join(self.__dir_info["local"]["setup"], "../../app", ".aux"): {
                "bind": join(self.dir_expr, ".aux"),
                "mode": "rw",
            },
        }

        container_name = "{}-{}-{}".format(self.name, subject_name, bug_id)
        container_id = container.get_container_id(container_name)
        if container_id:
            container.stop_container(container_id)
            container.remove_container(container_id)
        container_id = container.build_container(
            container_name, volume_list, image_name
        )
        parent_dirs = join(*self.dir_setup.split("/")[:-2])
        mkdir_cmd = "mkdir -p {}".format(parent_dirs)
        copy_local_cmd = "cp -rf {} {}".format("/scripts", self.dir_setup)
        self.run_command(container_id, mkdir_cmd, "/dev/null", "/")
        self.run_command(container_id, copy_local_cmd, "/dev/null", "/")
        return container_id

    def setup_experiment(self, bug_index, container_id, test_all):
        emitter.normal("\t\t[benchmark] preparing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        setup_error = False
        if not container_id:
            self.base_dir_experiment = os.path.abspath(
                os.path.dirname(__file__) + "/../../experiments/"
            )
            if os.path.isdir(self.dir_expr):
                utilities.execute_command("rm -rf {}".format(self.dir_expr))
            if not os.path.isdir(self.dir_logs):
                utilities.execute_command("mkdir -p {}".format(self.dir_logs))
        else:
            if not container.is_dir(container_id, self.dir_logs):
                self.run_command(
                    container_id, "mkdir -p {}".format(self.dir_logs), dir_path="/"
                )
        if self.deploy(bug_id, container_id):
            if self.config(bug_id, container_id):
                if self.build(bug_id, container_id):
                    if test_all:
                        if self.test_all(experiment_item, container_id):
                            emitter.success(
                                "\t\t\t[benchmark] setting up completed successfully"
                            )
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                            setup_error = True
                    else:
                        if self.test(bug_id, container_id):
                            emitter.success(
                                "\t\t\t[benchmark] setting up completed successfully"
                            )
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                            setup_error = True
                else:
                    emitter.error("\t\t\t[benchmark] build failed")
                    setup_error = True
            else:
                emitter.error("\t\t\t[benchmark] config failed")
                setup_error = True
        else:
            emitter.error("\t\t\t[benchmark] deploy failed")
            setup_error = True
        return setup_error

    def get_exp_image(self, bug_index, test_all):
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        exp_image_name = "{}-{}-{}".format(self.name, subject_name, bug_id).lower()
        if not container.is_image_exist(exp_image_name) or values.DEFAULT_REBUILD_ALL_IMAGES:
            emitter.warning("\t\t[warning] experiment not built")
            emitter.normal("\t\t\tpreparing/building experiment")
            self.build_experiment_image(bug_index, test_all, exp_image_name)
        else:
            emitter.success(
                "\t\t\t\tpre-built experiment found: {}".format(exp_image_name)
            )
        return exp_image_name

    @abc.abstractmethod
    def setup(self, bug_index, config_ig, test_all, use_container, is_multi):
        """Method documentation"""
        return

    @abc.abstractmethod
    def deploy(self, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def save_artefacts(self, dir_info, container_id):
        if container_id:
            dir_exp = dir_info["container"]["experiment"]
            dir_artifact = dir_info["container"]["artifacts"]
        else:
            dir_exp = dir_info["local"]["experiment"]
            dir_artifact = dir_info["local"]["artifacts"]

        emitter.normal("\t\t\tsaving experiment dev-patch")
        if self.list_artifact_dirs:
            for art_dir in self.list_artifact_dirs:
                art_dir_path = join(dir_exp, art_dir)
                copy_command = "cp -rf {} {}".format(art_dir_path, dir_artifact)
                self.run_command(container_id, copy_command, "/dev/null", "/")

        if self.list_artifact_files:
            for art_file in self.list_artifact_files:
                art_file_path = join(dir_exp, art_file)
                copy_command = "cp -f {} {}".format(art_file_path, dir_artifact)
                self.run_command(container_id, copy_command, "/dev/null", "/")
        return

    @abc.abstractmethod
    def clean(self, exp_dir_path, container_id):
        """Method documentation"""
        return
