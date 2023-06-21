import csv
import json
import os
import shutil

DATASET_PATH = os.path.join(os.getcwd(), "dataset", "vul4j_dataset.csv")
result = []
id = 0
with open(DATASET_PATH) as f:
    reader = csv.DictReader(f, delimiter=',', )
    for row in reader:
        vul_id = row['vul_id'].strip()
        cve_id = row['cve_id'].strip()

        repo_slug = row['repo_slug'].strip().split("/")[0]
        build_system = row['build_system'].strip()
        compliance_level = int(row['compliance_level'].strip())

        compile_cmd = row['compile_cmd'].strip()
        test_all_cmd = row['test_all_cmd'].strip()
        test_cmd = row['test_cmd'].strip()
        cmd_options = row['cmd_options'].strip()

        failing_module = row['failing_module'].strip()
        src_java_dir = row['src'].strip()
        src_classes_dir = row['src_classes'].strip()
        test_java_dir = row['test'].strip()
        test_classes_dir = row['test_classes'].strip()

        human_patch_url = row['human_patch'].strip()

        all_dependencies_jar_path = os.path.join("src", "target", "all-dependencies.jar")

        if failing_module != "root" and failing_module != "":
            src_java_dir = os.path.join(failing_module, src_java_dir)
            src_classes_dir = os.path.join(failing_module, src_classes_dir)
            test_java_dir = os.path.join(failing_module, test_java_dir)
            test_classes_dir = failing_module + '/' + test_classes_dir
            all_dependencies_jar_path = os.path.join("src", failing_module, "target", "all-dependencies.jar")
        else:
            failing_module = ""

        failing_tests = set()
        for failing_test in row['failing_tests'].strip().split(','):
            failing_tests.add(failing_test.split("#")[0])

        if row['build_system'].strip().lower() == 'maven':
            all_dependencies_jar_path_lst = [all_dependencies_jar_path]
        else:
            all_dependencies_jar_path_lst = []


        # create dep.sh script
        # script_content = "#!/bin/bash\n"
        # if compliance_level == '7':
        #     script_content += "export JAVA_HOME=$(echo $JAVA7_HOME)\n"
        # else:
        #     script_content += "export JAVA_HOME=$(echo $JAVA8_HOME)\n"

        # path_to_create = os.path.join(os.getcwd(), row['cve_id'].strip(), row['vul_id'].strip())
        # os.makedirs(path_to_create, 0o775, exist_ok=True)
        # with open(os.path.join(path_to_create, "deps.sh"), "w") as fd:
        #     fd.write(script_content)
        # os.remove(os.path.join(path_to_create, "deps.sh"))

        id += 1
        result.append(
            {
                "id": id,
                "subject": repo_slug,
                "bug_id": cve_id,
                "vul4j_id": vul_id,
                "failing_module": failing_module,
                "source_directory": src_java_dir,
                "class_directory": src_classes_dir,
                "test_directory": test_java_dir,
                "test_class_directory": test_classes_dir,
                "java_version": compliance_level,
                "build_system": row['build_system'].strip().lower(),
                "dependencies": all_dependencies_jar_path_lst,
                "compile_cmd": f"{compile_cmd} {cmd_options}",
                "test_all_cmd": test_all_cmd,
                "line_numbers": [],
                "failing_test": list(failing_tests),
                "passing_test": [],
                "count_neg": 0,
                "count_pos": 0,
                "test_timeout": 5,
            }
        )



root_project = os.getcwd()
os.chdir(root_project)
x = open("meta-data.json", "w")
x.write(json.dumps(result, indent=4))
x.close()
