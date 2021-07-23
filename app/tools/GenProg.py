import os
from app.tools import AbstractTool
from app.utilities import execute_command, error_exit
from app import definitions, values


class GenProg(AbstractTool):
    def __init__(self):
        self.name = "GenProg"

    def instrument(self, exp_dir_path, bug_id):
        print("\t[INFO] instrumenting for", self.name)
        self.log_instrument_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-instrument.log"
        if os.path.isfile(exp_dir_path + "/instrument.sh"):
            command_str = "cd " + exp_dir_path + "; bash instrument.sh;"
            command_str += " > {0} 2>&1".format(self.log_deploy_path)
            status = execute_command(command_str)
            return status
        else:
            error_exit("no instrumentation available for ", self.name)

    def repair(self, setup_dir_path, deploy_path, bug_id, timeout, count_pass, count_neg, fix_location, subject_name):
        print("\t[INFO] running repair with", self.name)
        self.log_output_path = definitions.DIR_LOGS + "/" + self.name + "-" + bug_id + "-instrument.log"
        timestamp_command = "echo $(date) > " + self.log_output_path
        execute_command(timestamp_command)
        repair_command = "cd {0}; timeout -k 5m {1}h  ".format(deploy_path + "/src", str(timeout))
        repair_command += "genprog --label-repair  "
        if fix_location:
            source_file, line_number = fix_location.split(":")
            with open(deploy_path + "/src/fault-loc", "w") as loc_file:
                loc_file.write(str(line_number))
            repair_command += " --fault-scheme line " \
                              " --fault-file fault-loc "
        repair_command += " --pos-tests {p_size} " \
                          " --neg-tests {n_size} " \
                          " --test-script \"bash /experiments/benchmark/{benchmark}/{subject}/{bug_id}/test.sh\" " \
            .format(bug_id=bug_id, p_size=count_pass, n_size=count_neg,
                    benchmark="ManyBugs", subject=subject_name)
        repair_command += " repair.conf >> {0} 2>&1 ".format(self.log_output_path)
        execute_command(repair_command)
        timestamp_command = "echo $(date) >> " + self.log_output_path
        execute_command(timestamp_command)
        return

    def preprocess(self, input):
        """Method documentation"""
        return

   
    def postprocess(self, input):
        """Method documentation"""
        return

   
    def archive(self, input):
        """Method documentation"""
        return