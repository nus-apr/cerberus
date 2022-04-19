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
        self.load()

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

    def setup_container(self, tool_name, bug_index, config_id, use_container):
        container_id = None
        if use_container:
            emitter.normal("\t\t[benchmark] preparing docker environment")
            experiment_item = self.experiment_subjects[bug_index - 1]
            bug_id = str(experiment_item[definitions.KEY_BUG_ID])
            subject_name = str(experiment_item[definitions.KEY_SUBJECT])
            self.setup_dir_path = "/setup"
            dir_setup_local = self.bench_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_setup_container = self.setup_dir_path + "/" + self.name + "/" + subject_name + "/" + bug_id
            dir_exp_local = definitions.DIR_EXPERIMENT + "/" + self.name + "/" + subject_name + "/" + bug_id
            if os.path.isdir(dir_exp_local):
                shutil.rmtree(dir_exp_local)
            dir_output_local = definitions.DIR_ARTIFACTS + "/" + str(config_id) + "-" + self.name + "-" + \
                               tool_name + "-" + subject_name + "-" + bug_id
            dir_aux_local = self.bench_dir_path + "/" + self.name + "/" + subject_name + "/.aux"
            dir_aux_container = "/experiments/benchmark/" + self.name + "/" + subject_name + "/.aux"
            dir_base_local = self.bench_dir_path + "/" + self.name + "/" + subject_name + "/base"
            dir_base_container = "/experiments/benchmark/" + self.name + "/" + subject_name + "/base"
            volume_list = {
                # dir_exp_local: {'bind': '/experiment', 'mode': 'rw'},
                self.log_dir_path: {'bind': '/logs', 'mode': 'rw'},
                dir_output_local: {'bind': '/output', 'mode': 'rw'},
                dir_setup_local: {'bind': dir_setup_container, 'mode': 'rw'},
                dir_aux_local: {'bind': dir_aux_container, 'mode': 'rw'},
                dir_base_local: {'bind': dir_base_container, 'mode': 'rw'},
                "/var/run/docker.sock": {'bind': "/var/run/docker.sock", 'mode': 'rw'}
            }
            container_id = container.get_container(tool_name, self.name, subject_name, bug_id, config_id)
            if container_id:
                container.stop_container(container_id)
                container.remove_container(container_id)
            container_id = container.build_container(tool_name, self.name, subject_name, bug_id, volume_list, config_id)
        return container_id

    def setup_experiment(self, directory_name, bug_index, config_id, container_id, test_all, tool_name):
        emitter.normal("\t\t[benchmark] preparing experiment subject")
        experiment_item = self.experiment_subjects[bug_index - 1]
        bug_id = str(experiment_item[definitions.KEY_BUG_ID])
        if self.deploy(directory_name, bug_id, config_id, container_id):
            if self.config(directory_name, bug_id, config_id, container_id, tool_name):
                if self.build(directory_name, bug_id, config_id, container_id):
                    if test_all:
                        if self.test_all(directory_name, experiment_item, config_id, container_id):
                            emitter.success("\t\t\t[benchmark] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                    else:
                        if self.test(directory_name, bug_id, config_id, container_id):
                            emitter.success("\t\t\t[benchmark] setting up completed successfully")
                        else:
                            emitter.error("\t\t\t[benchmark] testing failed")
                else:
                    emitter.error("\t\t\t[benchmark] build failed")
            else:
                emitter.error("\t\t\t[benchmark] config failed")
        else:
            emitter.error("\t\t\t[benchmark] deploy failed")

    @abc.abstractmethod
    def setup(self, tool_name, bug_index, config_ig, test_all, use_container):
        """Method documentation"""
        return

    @abc.abstractmethod
    def deploy(self, exp_dir_path, bug_id, config_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def config(self, exp_dir_path, bug_id, config_id, container_id, tool_name):
        """Method documentation"""
        return

    @abc.abstractmethod
    def build(self, exp_dir_path, bug_id, config_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test(self, exp_dir_path, bug_id, config_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def test_all(self, exp_dir_path, bug_id, config_id, container_id):
        """Method documentation"""
        return

    @abc.abstractmethod
    def save_artefacts(self, dir_exp, dir_artifact, container_id):
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

