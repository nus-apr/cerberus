import os
import sys

binary_name = sys.argv[1]
llvm_ir_path = binary_name + ".ll"
gdb_script_path = "gdb_script"
struct_list = []
with open(llvm_ir_path, "r") as input_file:
    content_lines = input_file.readlines()
    for line in content_lines:
        if "@" in line:
            break
        if "struct" in line:
            struct_name = line.split(" = ")[0].split(".")[1]
            struct_list.append(struct_name)

with open(gdb_script_path, "w") as out_file:
    for struct_name in struct_list:
        out_file.writelines("offsets-of \"{}\"\n".format(struct_name))
        out_file.writelines("printf \"\\n\"\n")

os.system("gdb -batch -silent -x gdb_script {} > def_file".format(binary_name))

