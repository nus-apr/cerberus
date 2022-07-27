import os
import json
import sys
import collections


def read_json(file_path):
    json_data = None
    if os.path.isfile(file_path):
        with open(file_path, "r") as in_file:
            content = in_file.readline()
            json_data = json.loads(content)
    return json_data


def fetch_function_nodes(translation_unit, source_file):
    function_node_list = []
    for ast_node in translation_unit["inner"]:
        node_type = ast_node["kind"]
        if node_type == "FunctionDecl":
            function_node_list.append(ast_node)
    return function_node_list


def fetch_operator_ranges(ast_tree):
    node_range_list = []
    if "kind" not in ast_tree.keys():
        return []
    if "inner" not in ast_tree.keys():
        return []
    for ast_node in ast_tree["inner"]:
        if "kind" not in ast_node.keys():
            continue
        node_type = ast_node["kind"]
        if node_type in ["UnaryOperator", "BinaryOperator", "ConditionalOperator"]:
            node_range = ast_node["range"]
            begin_loc = node_range["begin"]
            end_loc = node_range["end"]
            if "line" not in begin_loc.keys() or "line" not in end_loc.keys():
                continue
            start_line_no = int(begin_loc["line"])
            last_line_no = int(end_loc["line"]) - 1
            node_range_list.append((start_line_no, last_line_no))
        if "inner" in ast_node.keys():
            node_range_list = node_range_list + fetch_operator_ranges(ast_node)
    return node_range_list


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
        if node_type in ["IfStmt", "ForStmt", "WhileStmt", "DoStmt"]:
            node_list.append(ast_node)

        if "inner" in ast_node.keys():
            node_list = node_list + fetch_control_nodes(ast_node)
    return node_list


def fetch_condition_ranges(control_node_list):
    condition_range_list = []
    for control_node in control_node_list:
        node_type = control_node["kind"]
        if node_type in ["IfStmt", "WhileStmt"]:
            print(control_node)
            cond_node = control_node["inner"][0]
            cond_range_info = cond_node["range"]
            compound_range_info = None
            if "inner" in control_node["inner"][1].keys():
                compound_first_node = control_node["inner"][1]["inner"][0]
                compound_range_info = compound_first_node["range"]
            begin_loc = cond_range_info["begin"]
            end_loc = cond_range_info["end"]

            if "line" not in begin_loc.keys():
                continue
            start_line_no = int(begin_loc["line"])
            if "line" not in end_loc.keys():
                if compound_range_info:
                    end_loc = compound_range_info["begin"]
                    if "line" not in end_loc.keys():
                        continue
                    last_line_no = int(end_loc["line"]) - 1
            else:
                last_line_no = int(end_loc["line"])
            condition_range_list.append((start_line_no, last_line_no))
        elif node_type == "ForStmt":
            cond_node = control_node["inner"][0]
            compound_first_node = control_node["inner"][3]["inner"][0]
            cond_range_info = cond_node["range"]
            compound_range_info = compound_first_node["range"]
            begin_loc = cond_range_info["begin"]
            end_loc = cond_range_info["end"]

            if "line" not in begin_loc.keys():
                continue
            start_line_no = int(begin_loc["line"])
            if "line" not in end_loc.keys():
                end_loc = compound_range_info["begin"]
                if "line" not in end_loc.keys():
                    continue
                last_line_no = int(end_loc["line"]) - 1
            else:
                last_line_no = int(end_loc["line"])
            condition_range_list.append((start_line_no, last_line_no))
        elif node_type == "DoStmt":
            cond_node = control_node["inner"][-1]
            cond_range_info = cond_node["range"]
            compound_range_info = None
            if "inner" in cond_node.keys():
                compound_last_node = cond_node["inner"][-1]
                compound_range_info = compound_last_node["range"]
            begin_loc = cond_range_info["begin"]
            end_loc = cond_range_info["end"]

            if "line" not in begin_loc.keys():
                continue
            start_line_no = int(begin_loc["line"])
            if "line" not in end_loc.keys():
                if compound_range_info:
                    end_loc = compound_range_info["end"]
                    if "line" not in end_loc.keys():
                        continue
                    last_line_no = int(end_loc["line"]) - 1
            else:
                last_line_no = int(end_loc["line"])
            condition_range_list.append((start_line_no, last_line_no))

    print(condition_range_list)
    return condition_range_list


def fetch_call_ranges(ast_tree):
    node_range_list = []
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
            node_range = ast_node["range"]
            begin_loc = node_range["begin"]
            end_loc = node_range["end"]
            if "line" not in begin_loc.keys() or "line" not in end_loc.keys():
                continue
            start_line_no = int(begin_loc["line"])
            last_line_no = int(end_loc["line"]) - 1
            node_range_list.append((start_line_no, last_line_no))

        if "inner" in ast_node.keys():
            node_range_list = node_range_list + fetch_call_ranges(ast_node)
    return node_range_list


def generate_reversed_indexed_node_list(node_list):
    indexed_list = dict()
    for node in node_list:
        try:
            start_line = node["range"]["begin"]["line"]
            indexed_list[int(start_line)] = node
        except Exception as e:
            print(node["range"])
    sorted_node_list = collections.OrderedDict(
        sorted(indexed_list.items(), reverse=True)
    )
    return sorted_node_list


def generate_reversed_indexed_range_list(range_list):
    indexed_list = dict()
    for loc_range in range_list:
        start_line = loc_range[0]
        if int(start_line) in indexed_list.keys():
            existing_loc_range = indexed_list[start_line]
            existing_end_line = existing_loc_range[1]
            new_end_line = loc_range[1]
            if new_end_line > existing_end_line:
                indexed_list[int(start_line)] = loc_range
        else:
            indexed_list[int(start_line)] = loc_range
    sorted_node_list = collections.OrderedDict(
        sorted(indexed_list.items(), reverse=True)
    )
    return sorted_node_list
