import os
import json
import sys
import collections
from common import generate_reversed_indexed_range_list, fetch_control_nodes, read_json, \
	fetch_condition_ranges, fetch_call_ranges, fetch_function_nodes


def transform_single_line(sorted_range_list, orig_content):
	updated_content = orig_content
	for line_number, node_range in sorted_range_list.items():
		try:
			start_line_no = int(node_range[0])
			last_line_no = int(node_range[1])
			print(start_line_no, last_line_no)
			if start_line_no != last_line_no:
				no_lines = last_line_no - start_line_no
				merged_line = orig_content[start_line_no - 1].replace("\n", " ")
				print(merged_line)
				if "{" in merged_line:
					continue
				del_lines = []
				for i in range(0, no_lines):
					line_number = start_line_no + i
					next_line = orig_content[line_number].strip().replace("\n", " ").replace("\t", "")
					merged_line = merged_line.rstrip() + " " + next_line.lstrip()
					del_lines.append(line_number)
					if "{" in next_line:
						break
				for i in sorted(del_lines, reverse=True):
					del updated_content[i]
				merged_line = merged_line.replace("{", "{\n\t")
				print(merged_line)
				updated_content[start_line_no - 1] = merged_line
		except Exception as e:
			print()
			print(e)
	return updated_content


def merge():
	source_file = sys.argv[1]
	json_file = sys.argv[2]
	source_content = []
	formatted_content = []
	with open(source_file, "r") as s_f:
		source_content = s_f.readlines()
	translation_unit = read_json(json_file)
	function_node_list = fetch_function_nodes(translation_unit, source_file)
	print("# Function Nodes", len(function_node_list))
	control_node_list = []
	call_range_list = []
	condition_range_list = []
	for func_node in function_node_list:
		control_node_list = control_node_list + fetch_control_nodes(func_node)
		call_range_list = call_range_list + fetch_call_ranges(func_node)
	condition_range_list = fetch_condition_ranges(control_node_list)
	print("# Control Nodes", len(control_node_list))
	print("# Call Ranges", len(call_range_list))
	print("# Condition Ranges", len(condition_range_list))

	required_range_list = condition_range_list + call_range_list
	sorted_range_list = generate_reversed_indexed_range_list(required_range_list)
	merged_content = transform_single_line(sorted_range_list, source_content)
	with open("merged.c", "w") as out_file:
		out_file.writelines(merged_content)


if __name__ == "__main__":
	merge()
