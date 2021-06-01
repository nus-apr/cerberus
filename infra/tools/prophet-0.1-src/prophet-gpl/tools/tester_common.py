# Copyright (C) 2016 Fan Long, Martin Rianrd and MIT CSAIL 
# Prophet
# 
# This file is part of Prophet.
# 
# Prophet is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
# 
# Prophet is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with Prophet.  If not, see <http://www.gnu.org/licenses/>.
from os import getcwd, chdir
import subprocess

def get_fix_revisions(out_dir):
    ori_dir = getcwd();
    chdir(out_dir);
    subprocess.call(["git", "checkout", "master", "-f"]);
    p = subprocess.Popen(["git", "log"], stdout=subprocess.PIPE);
    chdir(ori_dir);
    (out, err) = p.communicate();
    lines = out.split("\n");
    # parse git log to get bug-fix revision and previous revision
    cur_revision = "";
    last_fix_revision = "";
    comment = "";
    last_is_author = False;
    ret = []
    for line in lines:
        tokens = line.strip("\n").strip(" ").split();
        if len(tokens) == 0:
            continue;
        if (len(tokens) == 2) and (tokens[0] == "commit") and (len(tokens[1]) > 10):
            cur_revision = tokens[1];
            if last_fix_revision != "":
                chdir(out_dir);
                p = subprocess.Popen(["git", "rev-list", "--parents", "-n", "1", last_fix_revision], stdout=subprocess.PIPE);
                chdir(ori_dir);
                (out, err) = p.communicate();
                tokens = out.split();
                if len(tokens) == 2:
                    chdir(out_dir);
                    p = subprocess.Popen(["git", "diff", "--name-only", last_fix_revision, last_fix_revision+"^1"], stdout=subprocess.PIPE);
                    chdir(ori_dir);
                    (out,err) = p.communicate();
                    out_lines = out.split("\n");
                    for out_line in out_lines:
                        name_str = out_line.strip();
                        idx = name_str.rfind(".");
                        extension = name_str[idx+1:];
                        if (extension == "c") or (extension == "h") or (extension == "cpp") or (extension == "hpp"):
                            ret.append((last_fix_revision, tokens[1], comment));
                            break;
            last_fix_revision = "";
            comment = "";
        elif (tokens[0] == "Date:") and last_is_author:
            year = int(tokens[5]);
            if (year < 2010):
                break;
        elif (tokens[0] != "Author:" and tokens[0] != "Merge:"):
            comment = comment + "\n" + line;
            is_fix = False;
            for token in tokens:
                if (token.lower() == "fixed") or (token.lower() == "bug") or (token.lower() == "fix"):
                    is_fix = True;
                    break;
            if is_fix:
                last_fix_revision = cur_revision;
        if tokens[0] == "Author:":
            last_is_author = True;
        else:
            last_is_author = False;
    return ret;

def extract_arguments(out_dir, src_file):
    ori_dir = getcwd();
    chdir(out_dir);
    # trigger the make again
    subprocess.call(["touch", src_file]);
    # eliminate the path, leave only the file name for search
    idx = src_file.rfind("/");
    if idx != -1:
        file_name = src_file[idx+1:];
    else:
        file_name = src_file;
    p = subprocess.Popen(["make", "--debug=j"], stdout = subprocess.PIPE);
    (out, err) = p.communicate();
    lines = out.strip().split("\n");
    directory = ".";
    last_line = "";
    for line in lines:
        strip_line = line.strip();
        if (len(strip_line) > 0) and (strip_line[len(strip_line) - 1] == "\\"):
            last_line = last_line + " " + strip_line[0:len(strip_line) - 1];
        else:
            if last_line != "":
                line = last_line + " " + line;
                last_line = "";
            if line.find("Entering directory") != -1:
                idx = line.find("Entering directory");
                idx1 = line.find("`", idx);
                idx2 = line.find("'", idx);
                directory = line[idx1 + 1:idx2];

            if line.find(file_name) != -1:
                tokens = line.strip().split();
                idx = 0;
                for i in range(0, len(tokens)):
                    if tokens[i] == "cc" or tokens[i] == "gcc":
                        idx = i + 1;
                        break;
                ret = "";
                for token in tokens[idx:]:
                    if token[0] == '`':
                        break;
                    if token == '&&':
                        break;
                    if token.find("excess-precision") != -1:
                        continue;
                    if token.find(file_name) == -1:
                        ret = ret + token + " ";
                chdir(ori_dir);
                return directory, ret;
    # we try another way to get around it
    subprocess.call(["touch", src_file]);
    p = subprocess.Popen(["make", "-n"], stdout = subprocess.PIPE);
    (out, err) = p.communicate();
    print out;
    lines = out.strip().split("\n");
    directory = ".";
    for line in lines:
        if line.find("Entering directory") != -1:
            idx = line.find("Entering directory");
            idx1 = line.find("`", idx);
            idx2 = line.find("'", idx);
            directory = line[idx1 + 1:idx2];
        if line.find(file_name) != -1:
            tokens = line.strip().split();
            idx = -1;
            for i in range(0, len(tokens)):
                if tokens[i] == "cc" or tokens[i] == "gcc" or tokens[i].find(";gcc") != -1:
                    idx = i + 1;
                    break;
            if idx != -1:
                ret = "";
                for token in tokens[idx:]:
                    if token[0] == '`':
                        break;
                    if token == '&&':
                        break;
                    if token.find("excess-precision") != -1:
                        continue;
                    if token.find(file_name) == -1:
                        ret = ret + token + " ";
                chdir(ori_dir);
                return directory, ret;
    chdir(ori_dir);
    return "","";

