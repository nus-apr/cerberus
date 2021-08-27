import os
import glob
import json
import sys
from os import listdir
from os.path import isfile, join


meta_file_path = sys.argv[1]
patch_dir = sys.argv[2]
result_list = []

patch_data = dict()
partition_data = dict()
if os.path.isfile(meta_file_path):
    with open(meta_file_path, 'r') as in_file:
        content = in_file.readlines()
        # partition_data = json.loads(content)
        partition_id = 0
        partition_data[partition_id] = list()
        for line in content:
            partition_data[partition_id].append(line.replace("{", "").replace("}", "").replace(",", "").strip())
            if "}" in line:
                partition_id = partition_id + 1
                partition_data[partition_id] = list()
        in_file.close()
    if os.path.isdir(patch_dir):
        output_patch_list = [f for f in listdir(patch_dir) if isfile(join(patch_dir, f))]
        for patch_file in output_patch_list:
            if "partition.txt" in patch_file:
                continue
            syntax_dist, gen_order, patch_id = patch_file.split("_")
            patch_id = patch_id.replace(".patch", "")

            for partition_id in partition_data:
                partition_list = partition_data[partition_id]
                if patch_id in partition_list:
                    patch_data[patch_id] = [partition_id, int(syntax_dist), int(gen_order)]
        filtered_patch_list = dict()
        for patch_id in patch_data:
            partition_id, syntax_dist, gen_order = patch_data[patch_id]
            if partition_id not in filtered_patch_list:
                filtered_patch_list[partition_id] = (patch_id, syntax_dist, gen_order)
            else:
                sel_patch_id, min_syntax_dist, min_gen_order = filtered_patch_list[partition_id]
                if syntax_dist < min_syntax_dist:
                    filtered_patch_list[partition_id] = (patch_id, syntax_dist, gen_order)
                elif syntax_dist == min_syntax_dist:
                    if gen_order < min_gen_order:
                        filtered_patch_list[partition_id] = (patch_id, syntax_dist, gen_order)

        for partition_id in filtered_patch_list:
            patch_id, syntax_dist, gen_order = filtered_patch_list[partition_id]
            print("{0}_{1}_{2}.patch".format(syntax_dist, gen_order, patch_id))

