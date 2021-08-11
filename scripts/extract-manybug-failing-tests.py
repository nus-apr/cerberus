import os
import glob
meta_file_path = "manybugs-id-list"
result_list = []
with open(meta_file_path, "r") as meta_file:
    id_list = meta_file.readlines()
    for bug_id in id_list:
        bug_id = bug_id.strip().replace("\n", "")
        if not os.path.isdir(bug_id):
            init_command = "wget https://repairbenchmarks.cs.umass.edu/ManyBugs/scenarios/{id}.tar.gz; tar xf {id}.tar.gz".format(id=bug_id)
            os.system(init_command)
        if os.path.isdir(bug_id):
            bug_dir = os.getcwd() + "/" + bug_id
            bug_fail_file_path = bug_dir + "/bug-failures"
            fix_fail_file_path = bug_dir + "/fix-failures"
            with open(bug_fail_file_path, 'r', encoding='utf8', errors="ignore") as log_file:
                bug_fail_list = log_file.readlines()
            with open(fix_fail_file_path, 'r', encoding='utf8', errors="ignore") as log_file:
                fix_fail_list = log_file.readlines()

            repaired_list = list(set(bug_fail_list) - set(fix_fail_list))
            repaired_list = [int(x.strip().replace("\n", "")) for x in repaired_list]
            result_list.append((bug_id, sorted(repaired_list)))

for result in result_list:
    print(result[0], result[1])
