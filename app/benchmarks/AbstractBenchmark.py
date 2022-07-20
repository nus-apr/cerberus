import abc
import os
import json
import shutil
from app import emitter, utilities, container, definitions


class AbstractBenchmark:
    experiment_subjects = []
    meta_file = None
    bench_dir_path = None
    name = None
    image_name = None
    dir_logs = ""
    dir_logs_container = ""
    dir_expr = ""
    dir_expr_container = ""
    dir_base_expr = ""
    dir_inst = ""
    dir_setup = ""
    dir_setup_container = ""
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
        self.meta_file = self.bench_dir_path + "/" + self.name + "/meta-data.json"
        self.image_name = "{}-benchmark".format(self.name)
        self.build_benchmark_image()
        self.load()


    def update_dir_info(self, dir_info):
        self.dir_expr_container = dir_info["container"]["experiment"]
        self.dir_logs_container = dir_info["container"]["logs"]
        self.dir_setup_container = dir_info["container"]["setup"]
        self.dir_base_expr = "/experiment/"
        self.dir_expr = dir_info["local"]["experiment"]
        self.dir_logs = dir_info["local"]["logs"]
        self.dir_setup = dir_info["local"]["setup"]
        self.dir_base_expr = definitions.DIR_EXPERIMENT


    def get_list(self):
        return self.experiment_subjects

    def load(self):
        emitter.normal("loading experiment meta-data")
        if os.path.isfile(self.meta_file):
            with open(self.meta_file, 'r') as in_file:
                json_data = json.load(in_file)
                if json_data:
                    self.experiment_subjects = json_data
                    self.size = len(json_data)
                else:
                    utilities.error_exit("could not load meta-data from ", self.meta_file)
        else:
            utilities.error_exit("Meta file does not exist")
        return

    def run_command(self, command_str, log_file_path, exp_dir_path, container_id):
        if container_id:
            exit_code, output = container.exec_command(container_id, command_str, exp_dir_path)
            stdout, stderr = output
            if "/dev/null" not in log_file_path:
                with open(log_file_path, 'w') as log_file:
                    if stdout:
                        log_file.writelines(stdout.decode("utf-8"))
                    if stderr:
                        log_file.writelines(stderr.decode("utf-8"))
        else:
            command_str = "cd " + exp_dir_path + ";" + command_str
            command_str += " > {0} 2>&1".format(log_file_path)
            exit_code = utilities.execute_command(command_str)
        return exit_code

    def build_benchmark_image(self):
        if not container.is_image_exist(self.image_name):
            emitter.warning("\tbenchmark environment not found")
            emitter.normal("\tbuilding benchmark environment")
            container.build_benchmark_image(self.image_name)
        else:
            emitter.success("\t\tpre-built benchmark environment found")


    def build_experiment_image(self, bug_index, test_all, exp_image_name):
        container_id = self.setup_container(bug_index, self.image_name)
        self.setup_experiment(self.dir_setup_container, bug_index, container_id, test_all)
        container_obj = container.get_container(container_id)
        container_obj.commit(exp_image_name)


    def setup_container(self, bug_index, image_name):
        container_id = None
        emitter.normal("\t\t[benchmark] preparing experiment environment")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        dir_exp_local = definitions.DIR_EXPERIMENT + "/" + self.name + "/" + subject_name + "/" + bug_id

        if os.path.isdir(dir_exp_local):
            shutil.rmtree(dir_exp_local)

        volume_list = {
            # dir_exp_local: {'bind': '/experiment', 'mode': 'rw'},
            self.dir_logs: {'bind': '/logs', 'mode': 'rw'},
            self.dir_setup: {'bind': self.dir_setup_container, 'mode': 'rw'},
            "/var/run/docker.sock": {'bind': "/var/run/docker.sock", 'mode': 'rw'}
        }
        container_name = self.name + "-" + subject_name + "-" + bug_id
        container_id = container.get_container_id(container_name)
        if container_id:
            container.stop_container(container_id)
            container.remove_container(container_id)
        container_id = container.build_container(container_name, volume_list, image_name)
        return container_id

    def setup_experiment(self, directory_name, bug_index, container_id, test_all):
        emitter.normal("\t\t[benchmark] preparing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        if self.deploy(directory_name, bug_id, container_id):
            if self.config(directory_name, bug_id, container_id):
                if self.build(directory_name, bug_id, container_id):
                    if test_all:
                        if self.test_all(directory_name, experiment_item, container_id):
                            emitter.success("\t\t\t[benchmark] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                    else:
                        if self.test(directory_name, bug_id, container_id):
                            emitter.success("\t\t\t[benchmark] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                else:
                    emitter.error("\t\t\t[benchmark] build failed")
            else:
                emitter.error("\t\t\t[benchmark] config failed")
        else:
            emitter.error("\t\t\t[benchmark] deploy failed")


    def get_exp_image(self, bug_index, test_all):
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        subject_name = str(experiment_item[definitions.KEY_SUBJECT])
        exp_image_name = "{}-{}-{}".format(self.name, subject_name, bug_id).lower()
        if not container.is_image_exist(exp_image_name):
            emitter.warning("\t\t[warning] experiment not built")
            emitter.normal("\t\t\tpreparing/building experiment")
            self.build_experiment_image(bug_index, test_all, exp_image_name)
        else:
            emitter.success("\t\t\t\tpre-built experiment found")
        return exp_image_name


    @abc.abstractmethod
    def setup(self, bug_index, config_ig, test_all, use_container, is_multi):
        """Method documentation"""
        return

    @abc.abstractmethod
    def deploy(self, setup_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, setup_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, setup_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, setup_dir_path, bug_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, setup_dir_path, bug_id, container_id):
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
                art_dir_path = dir_exp + "/" + art_dir
                copy_command = "cp -rf " + art_dir_path + " " + dir_artifact
                self.run_command(copy_command, "/dev/null", "/", container_id)

        if self.list_artifact_files:
            for art_file in self.list_artifact_files:
                art_file_path = dir_exp + "/" + art_file
                copy_command = "cp -f" + art_file_path + " " + dir_artifact
                self.run_command(copy_command, "/dev/null", "/", container_id)
        return

    @abc.abstractmethod
    def clean(self, exp_dir_path, container_id):
        """Method documentation"""
        return

