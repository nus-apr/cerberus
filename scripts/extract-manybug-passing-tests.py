import os
import json

directory = "/experiments/benchmark/manybugs"
subject_list = [x[0] for x in os.walk(directory)]
result_list = dict()


def write_as_json(data_list, output_file_path):
    content = json.dumps(data_list)
    with open(output_file_path, 'w') as out_file:
        out_file.writelines(content)


for subject in subject_list:
    id_list = subject_list = [x[0] for x in os.walk(directory + "/" + subject)]
    for bug_id in id_list:
        exp_dir = "/experiments/benchmark/manybugs/" + subject + "/" + bug_id
        data_dir = "/data/manybugs/" + subject + "/" + bug_id
        test_all = data_dir + "/tests.all.txt"
        test_log = exp_dir + "/test.log"

        if os.path.isfile(test_all):
            pass_list = []
            with open(test_all, "r") as t_file:
                test_list = t_file.readlines()

            if os.path.isfile(test_log):
                with open(test_log) as log_file:
                    log_lines = log_file.readlines()
                    test_case = None
                    test_status = None
                    for line in log_lines[1:]:
                        if test_case is None:
                            test_case = line.strip().replace("\n", "")
                        else:
                            test_status = line

                        if test_status is not None:
                            if "PASS" in test_status:
                                pass_list.append(test_list.index(test_case))
                            test_status = None
                            test_case = None

            result_list[subject + "-" + bug_id] = pass_list

write_as_json(result_list, "test.json")
