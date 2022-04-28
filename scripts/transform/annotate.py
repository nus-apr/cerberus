import os
import json
import sys
import collections
from common import generate_reversed_indexed_node_list, fetch_control_nodes, read_json, fetch_function_nodes


def annotate_jump(sorted_node_list, orig_content):
	updated_content = orig_content
	for line_number, c_node in sorted_node_list.items():
		node_range = c_node["range"]
		node_type = c_node["kind"]
		try:
			start_line_no = int(node_range["begin"]["line"])
			last_line_no = int(node_range["end"]["line"])
			child_list = c_node["inner"]
			if node_type == "IfStmt":
				compound_node = child_list[1]
				compound_range = compound_node["range"]
				last_line_no = int(compound_range["end"]["line"])
			start_line = updated_content[start_line_no - 1]
			start_line = " /* jump:{} */".format(last_line_no) + start_line
			updated_content[start_line_no - 1] = start_line
		except Exception as e:
			print(c_node)
	return updated_content


def annotate():
	source_file = sys.argv[1]
	json_file = sys.argv[2]
	source_content = []
	formatted_content = []
	with open(source_file, "r") as s_f:
		source_content = s_f.readlines()
	translation_unit = read_json(json_file)
	function_node_list = fetch_function_nodes(translation_unit, source_file)
	for ast_node in translation_unit["inner"]:
		node_type = ast_node["kind"]
		if node_type == "FunctionDecl":
			function_node_list.append(ast_node)

	print("# Function Nodes", len(function_node_list))
	control_node_list = []
	for func_node in function_node_list:
		control_node_list = control_node_list + fetch_control_nodes(func_node)

	print("# Control Nodes", len(control_node_list))
	sorted_control_node_list = generate_reversed_indexed_node_list(control_node_list)
	updated_content = annotate_jump(sorted_control_node_list, source_content)
	with open("annotated.c", "w") as out_file:
		out_file.writelines(updated_content)


if __name__ == "__main__":
	annotate()

