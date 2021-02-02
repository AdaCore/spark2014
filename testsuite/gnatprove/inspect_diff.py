#!/usr/bin/env python

"""
This script will first do a git diff, then inspect it and then try to open
the files corresponding to locations in the diff with emacs while interactively
asking to user if diffs are ok. It uses file /tmp/a.out as temporary.
It assumes that it is launched from testsuite/gnatprove. Also, it performs git
add with the comment given (populate the commit_msg etc) if the file is said
to be ok by the user.
"""

import os
import subprocess
import re

# TODO it is unnecessary to use a file here.
NAME_OF_TMP = "/tmp/a.out"
regexp = re.compile(r"a/testsuite/gnatprove/.*\.out")


def do_git_diff(tmp):
    with open(tmp, "w") as outfile:
        subprocess.call(["git", "diff", "--ignore-submodules", "."], stdout=outfile)


def get_result(result_file):
    fd = open(result_file, "r")
    tmp = fd.read()
    fd.close()
    return tmp


def get_file_name_from_diff(f):
    m = regexp.match(f)
    if m is None:
        print("Error cannot find filename in line " + f)
        exit(1)
    else:
        msg = m.group()
        # TODO hack on number to remove the a/testsuite/gnatprove at the
        # beginning and /test.out at the end (to get the directory)
        return msg[22:]


def print_by_line(f):
    for a in f:
        print(a)


def stage_file(f):
    subprocess.call(["git", "add", f])
    print(f + "staged")


""" This script is not optimal. This is known that splitting several times on
    several different regexp is not optimal.
"""


def iter_on_file(f):
    current_subfile = ""
    commit_msg = "================ COMMIT MSG ===================="
    cur_comments = []
    is_ok_to_stage = True
    if not os.path.exists(f):
        print("Error: file " + f + " does not exist")
        print(commit_msg)
        exit(1)

    file_out = str(get_result(f))
    file_list_diff = list(file_out.split("\n--- "))[1:]
    print(len(file_list_diff))
    for file_diff in file_list_diff:
        line_files = file_diff.splitlines()
        is_ok_to_stage = True
        current_subfile = get_file_name_from_diff(line_files[0])
        current_subdir = current_subfile[:-8]  # Hack to remove /test.out
        print("current_subfile: " + current_subfile)

        for line in line_files[1:]:
            if is_ok_to_stage and line[0] == "-":
                try:
                    # split on the first 3 ':'
                    not_ambiguous_l = line[1:].split(":", 3)
                    file_name = current_subdir + not_ambiguous_l[0]
                    print_by_line(line_files)
                    print("starting Emacs")
                    f = subprocess.call(["emacs", file_name])
                    try:
                        f.wait()
                    except Exception:
                        print("Exit Emacs")
                    # _line = not_ambiguous_l[1]
                    # _col = not_ambiguous_l[2]
                    # msg = not_ambiguous_l[3]
                    key = input(
                        "Is the diff ok [y, n] (or e for exit)"
                        "(or a to validate the complete file) ?"
                    )
                    if key == "a":
                        break
                    if key != "y":
                        if key == "e":
                            print("Exited after user input")
                            print(commit_msg)
                            exit(1)
                        is_ok_to_stage = False
                    print(file_name)
                except Exception:
                    print("Error: " + line)
                    is_ok_to_stage = False
        if is_ok_to_stage:
            print("current_comments are:")
            print(cur_comments)
            comment = input(
                "Insert a comment about the current file diffs"
                "(if you saw your comment already type"
                "0 to 4)\n"
            )
            try:
                if comment == "0":
                    comment = cur_comments[0]
                elif comment == "1":
                    comment = cur_comments[1]
                elif comment == "2":
                    comment = cur_comments[2]
                elif comment == "3":
                    comment = cur_comments[3]
                elif comment == "4":
                    comment = cur_comments[4]
                else:
                    cur_comments.append(comment)
            except Exception:
                cur_comments.append(comment)
            stage_file(current_subfile)
            commit_msg = commit_msg + "\n" + "* testsuite/gnatprove/"
            commit_msg = commit_msg + current_subfile + "\n" + comment
            print("it was ok to stage")
        else:
            print("Not ok to stage")
    print(commit_msg)


do_git_diff(NAME_OF_TMP)
iter_on_file(NAME_OF_TMP)
