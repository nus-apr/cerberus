import os
import json
import sys
import collections
from common import generate_reversed_indexed_list, fetch_control_nodes, read_json, \
	fetch_condition_nodes, fetch_call_nodes


def transform_single_line(sorted_node_list, orig_content):
	updated_content = orig_content
	for line_number, c_node in sorted_node_list.items():
		node_range = c_node["range"]
		try:
			start_line_no = int(node_range["begin"]["line"])
			last_line_no = int(node_range["end"]["line"])
			if start_line_no != last_line_no:
				no_lines = last_line_no - start_line_no
				merged_line = updated_content[start_line_no - 1]
				for i in range(0, no_lines):
					line_number = start_line_no + i
					next_line = updated_content[line_number].strip()
					merged_line = merged_line + next_line
					del updated_content[line_number]
				updated_content[start_line_no - 1] = merged_line
		except Exception as e:
			print(c_node)
	return updated_content


def merge():
	source_file = sys.argv[1]
	json_file = sys.argv[2]
	source_content = []
	formatted_content = []
	with open(source_file, "r") as s_f:
		source_content = s_f.readlines()
	translation_unit = read_json(json_file)
	function_node_list = []
	for ast_node in translation_unit["inner"]:
		node_type = ast_node["kind"]
		if node_type == "FunctionDecl":
			function_node_list.append(ast_node)

	print("# Function Nodes", len(function_node_list))
	control_node_list = []
	condition_node_list = []
	call_node_list = []
	for func_node in function_node_list:
		control_node_list = control_node_list + fetch_control_nodes(func_node)
		call_node_list = control_node_list + fetch_call_nodes(func_node)

	condition_node_list = condition_node_list + fetch_condition_nodes(control_node_list)
	print("# Control Nodes", len(control_node_list))
	print("# Call Nodes", len(call_node_list))
	print("# Condition Nodes", len(condition_node_list))

	required_node_list = call_node_list + condition_node_list
	sorted_node_list = generate_reversed_indexed_list(required_node_list)
	merged_content = transform_single_line(sorted_node_list, source_content)
	with open("formatted.c", "w") as out_file:
		out_file.writelines(merged_content)


if __name__ == "__main__":
	merge()
