import os

labs = [x for x in os.listdir() if not os.path.isfile(x) and "Lab" in x]

file = open("meta-data.candidate.json", "w")
file.write("[")
id = 0
for lab in labs:
    for problem_id in os.listdir(lab):
        for bug_id in [
            x for x in os.listdir(os.path.join(lab, problem_id)) if "_buggy" in x
        ]:
            id = id + 1
            name = bug_id.split("_")[0]
            data = """
            {{
                "id":"{id}",
                "subject":"{lab}",
                "bug_id":"{problem_id}",
                "source_file": "{bug_id}",
                "line_numbers": [],
                "failing_test": "1",
                "passing_test": "",
                "count_neg": "1",
                "count_pos": "0",
                "binary_path": "",
                "crash_input": "",
                "exploit_file_list": [{inputs}],
                "test_timeout": 5,
                "bug_type": ""

            }},
            """.format(
                id=id,
                lab=lab,
                name=name,
                problem_id=problem_id,
                bug_id=bug_id,
                inputs=",".join(
                    f'"{x}"'
                    for x in os.listdir(os.path.join(lab, "test"))
                    if problem_id in x and "in" in x
                ),
            )
            file.write(data)

file.write("]")
file.close()
