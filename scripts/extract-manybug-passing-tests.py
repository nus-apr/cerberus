import os
import json

directory = "/experiments/benchmark/manybugs"
sub_dir_list = [x[0] for x in os.walk(directory)]
result_list = dict()
subject_list = []

for dir_path in sub_dir_list[1:]:
    subject_name = dir_path.split("/")[4]
    subject_list.append(subject_name)
subject_list = list(set(subject_list))


def write_as_json(data_list, output_file_path):
    content = json.dumps(data_list)
    with open(output_file_path, 'w') as out_file:
        out_file.writelines(content)


for subject in subject_list:
    sub_dir_list = [x[0] for x in os.walk(directory + "/" + subject)]
    id_list = []
    for dir_path in sub_dir_list[1:]:
        bug_id = dir_path.split("/")[5]
        id_list.append(bug_id)
    id_list = list(set(id_list))
    for bug_id in id_list:
        exp_dir = "/experiments/benchmark/manybugs/" + subject + "/" + bug_id
        data_dir = "/data/manybugs/" + subject + "/" + bug_id
        test_all = data_dir + "/tests.all.txt"
        test_log = exp_dir + "/test.log"

        if os.path.isfile(test_all):
            pass_list = []
            with open(test_all, "r") as t_file:
                test_list = [x.strip().replace("\n", "") for x in t_file.readlines()]

            if os.path.isfile(test_log):
                with open(test_log) as log_file:
                    log_lines = log_file.readlines()
                    test_case = None
                    test_status = None
                    for line in log_lines:
                        if test_case is None:
                            test_case = line.split(": ")[1].strip().replace("\n", "")
                        else:
                            test_status = line

                        if test_status is not None:
                            if "PASS" in test_status:
                                pass_list.append(test_list.index(test_case))
                            test_status = None
                            test_case = None

            result_list[subject + "-" + bug_id] = pass_list

write_as_json(result_list, "test.json")
