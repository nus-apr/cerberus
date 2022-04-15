import os
import json
import sys
import collections

source_file = sys.argv[1]
json_file = sys.argv[2]
source_content = []
formatted_content = []

with open(source_file, "r") as s_f:
	source_content = s_f.readlines()

def read_json(file_path):
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, 'r') as in_file:
            content = in_file.readline()
            json_data = json.loads(content)
    return json_data

def fetch_control_nodes(ast_tree):
	node_list = []
	if "kind" not in ast_tree.keys():
		return []
	node_type = ast_tree["kind"]
	
	if "inner" not in ast_tree.keys():
		return []
	for ast_node in ast_tree["inner"]:
		if "kind" not in ast_node.keys():
			continue
		node_type = ast_node["kind"]
		if node_type in ["IfStmt", "ForStmt", "WhileStmt"]:
			node_list.append(ast_node)	
	
		if "inner" in ast_node.keys():
				node_list = node_list + fetch_control_nodes(ast_node)

	return node_list


translation_unit = read_json(json_file)
#print(source_ast)


function_node_list = []

for ast_node in translation_unit["inner"]:
	node_type = ast_node["kind"]
	if node_type == "FunctionDecl":
		function_node_list.append(ast_node)


print(len(function_node_list))
control_node_list = []
for func_node in function_node_list:
	control_node_list = control_node_list + fetch_control_nodes(func_node)

print(len(control_node_list))
indexed_control_node_list = dict()
for c_node in control_node_list:
	try:
		start_line = c_node["range"]["begin"]["line"]
		indexed_control_node_list[int(start_line)] = c_node
	except Exception as e:
		print(c_node["range"])
sorted_control_node_list = collections.OrderedDict(sorted(indexed_control_node_list.items(), reverse=True))
print(sorted_control_node_list.keys())
print(len(sorted_control_node_list.keys()))


for line_number, c_node in sorted_control_node_list.items():
	node_range = c_node["range"]
	try:
		start_line_no = int(node_range["begin"]["line"])
		last_line_no = int(node_range["end"]["line"])
		child_list = c_node["inner"]
		start_line = source_content[start_line_no - 1]
		start_line = " /* jump:{} */".format(last_line_no) + start_line
		source_content[start_line_no-1] = start_line
	except Exception as e:
		print(c_node)



with open("formatted.c", "w") as out_file:
	out_file.writelines(source_content)

