import os
import json
import sys
import collections


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


def fetch_condition_nodes(control_node_list):
	condition_node_list = []
	for control_node in control_node_list:
		node_type = control_node["kind"]
		cond_node = None
		if node_type in ["IfStmt", "WhileStmt"]:
			cond_node = control_node["inner"][0]
		if cond_node:
			condition_node_list.append(cond_node)
	return condition_node_list


def fetch_call_nodes(ast_tree):
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
		if node_type in ["CallExpr"]:
			node_list.append(ast_node)

		if "inner" in ast_node.keys():
			node_list = node_list + fetch_call_nodes(ast_node)
	return node_list


def generate_reversed_indexed_list(node_list):
	indexed_list = dict()
	for node in node_list:
		try:
			start_line = node["range"]["begin"]["line"]
			indexed_list[int(start_line)] = node
		except Exception as e:
			print(node["range"])
	sorted_node_list = collections.OrderedDict(sorted(indexed_list.items(), reverse=True))
	return sorted_node_list

