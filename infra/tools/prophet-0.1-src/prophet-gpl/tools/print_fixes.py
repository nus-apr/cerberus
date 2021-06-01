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

def print_fixes(out_dir):
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
    cnt = 0;
    last_is_author = False;
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
                    print "Fix Revision: " + last_fix_revision;
                    print "Previous Revision: " + tokens[1];
                    print "Comment:";
                    print comment;
                    cnt = cnt + 1;
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
    print "Total fix revision found: " + str(cnt);

