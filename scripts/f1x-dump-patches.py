import multiprocessing as mp
import time
import os
import sys
import re
import shlex

LIMIT_PATCHES = 250000


def mute():
    sys.stdout = open(os.devnull, "w")
    sys.stderr = open(os.devnull, "w")


pool = mp.Pool(mp.cpu_count(), initializer=mute)
result_list = []


def collect_result(result):
    global result_list
    result_list.append(result)


def collect_result_timeout(result):
    global result_list, expected_count
    result_list.append(result)
    if len(result_list) == expected_count:
        pool.terminate()


def collect_result_one(result):
    global result_list, found_one
    result_list.append(result)
    if result[0] is True:
        found_one = True
        pool.terminate()


def generate_patch(p_str, src_file, id, dir_exp, orig_file):
    os.chdir(dir_exp)
    fix_file = "/tmp/{}.fix".format(id)
    # os.system("cp {} {}".format(src_file, fix_file))
    # print("f1x-transform {} --apply --bl {} --bc {} --el {} --ec {} --patch {}".
    #          format(src_file, sl, sc, el, ec, p_str))
    cmd = 'KEYWORD="{}";'.format(p_str.replace("&", "\&"))
    # cmd += "ESCAPED_KEYWORD=$(printf '%s\n' \"$KEYWORD\" | sed -e 's/[]\/$*.^[]/\\&/g');"
    # cmd += "ESCAPED_KEYWORD=$(echo $KEYWORD | sed -e 's/\\/\\\\/g; s/\//\\\//g; s/&/\\\&/g');"
    cmd += 'sed "s/F1X_EXPRESSION_PLACEHOLDER/$KEYWORD/g" {} > {}'.format(
        src_file, fix_file
    )
    # cmd += "sed \"s/F1X_EXPRESSION_PLACEHOLDER/$ESCAPED_KEYWORD/g\" {} > {}".format(src_file, fix_file)
    os.system(cmd)
    # os.system("sed 's/F1X_EXPRESSION_PLACEHOLDER/{}/g' {} > {}".format(p_str, src_file, fix_file))
    # print(cmd)
    patch_file = "/output/patches/{}_f1x.patch".format(id)
    os.system("diff -U 0 {} {} > {}".format(orig_file, fix_file, patch_file))
    # os.system("cp {} {}".format(fix_file, src_file))


def generate_patches(source_file, dir_exp):
    global pool, result_list, LIMIT_PATCHES
    result_list = []
    loc_list = []
    dir_patch = "/output/patches"
    if not os.path.isdir(dir_patch):
        os.makedirs(dir_patch)
    file_space = dir_exp + "/patch-space"
    pool = mp.Pool(mp.cpu_count(), initializer=mute)
    back_up = "{}_bk".format(source_file)
    os.system("cp {0} {0}_bk".format(source_file))
    # print("starting parallel computing")
    with open(file_space, "r") as f:
        patch_space = f.readlines()
        patch_id = 0
        loc_id = 0
        for patch_desc in patch_space[:LIMIT_PATCHES]:
            patch_id = patch_id + 1
            patch_info = patch_desc.split(" ")
            sl = patch_info[2]
            sc = patch_info[3]
            el = patch_info[4]
            ec = patch_info[5]
            patch_loc = patch_info[-1]
            if patch_loc not in loc_list:
                loc_list.append(patch_loc)
                loc_id = loc_id + 1
                transform_file = "/tmp/f1x_{}".format(loc_id)
                os.system(
                    'f1x-transform {} --apply --bl {} --bc {} --el {} --ec {} --patch "{}"'.format(
                        source_file, sl, sc, el, ec, "F1X_EXPRESSION_PLACEHOLDER"
                    )
                )
                # print("f1x-transform {} --apply --bl {} --bc {} --el {} --ec {} --patch \"{}\"".format(source_file, sl, sc, el, ec, "F1X_EXPRESSION_PLACEHOLDER"))
                os.system("cp {} {}".format(source_file, transform_file))
                os.system("cp {0}_bk {0}".format(source_file))
                # print("cp {0}_bk {0}".format(source_file))
            else:
                loc_id = loc_list.index(patch_loc) + 1
                transform_file = "/tmp/f1x_{}".format(loc_id)
            patch_str = patch_desc.split(" in ")[0].replace(
                " ".join(patch_info[:6]), ""
            )
            # generate_patch(patch_str, transform_file, patch_id, dir_exp, back_up)
            pool.apply_async(
                generate_patch,
                args=(patch_str, transform_file, patch_id, dir_exp, back_up),
                callback=collect_result,
            )

    pool.close()
    # print("waiting for thread completion")
    pool.join()
    return result_list


# print(sys.argv)
src_file = sys.argv[1]
dir_exp = sys.argv[2]
start = time.time()
# print(start)
# print("args: {} {}".format(src_file, dir_exp))
generate_patches(src_file, dir_exp)
end = time.time()
# print(end)
d = end - start
# print(d)
