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
            diff_dir = os.getcwd() + "/" + bug_id + "/diffs/"
            file_list = glob.glob(diff_dir + '/**/*.*', recursive=True)
            if len(file_list) == 3:
                commit = bug_id.split("-")[-2]
                orig_file_path = ""
                diff_file_path = ""
                for file_name in file_list:
                    rel_file_path = file_name.replace(diff_dir, "")
                    if commit in rel_file_path:
                        orig_file_path = rel_file_path
                    if "diff" in rel_file_path:
                        diff_file_path = file_name
                with open(diff_file_path, 'r', encoding='utf8',errors="ignore") as diff_file:
                    content = diff_file.readlines()
                    line_list_str = ""
                    for line in content:
                        if line[0] not in [">", "<", "-"]:
                            line_list_str += line.strip().replace(",", "-") + ":"
                if line_list_str.count(":") > 3:
                    result_list.append((orig_file_path, "multiple-lines"))
                else:
                    result_list.append((orig_file_path, line_list_str))
            else:
                result_list.append(("multiple-files", "-"))


for result in result_list:
    print(result[0], result[1])
