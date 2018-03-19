#!/usr/bin/env python

import os.path

check_list = [os.path.join("gnat2why", "spark", "spark_definition.adb")]

cur_file = ""

linecount = 1


def is_comment_line(s):
    return s.startswith("--")


def is_empty_line(s):
    return len(s.strip('- ')) == 0


def print_error(s):
    global linecount
    global cur_file
    print cur_file + ":" + str(linecount) + ": " + s


def check_first_line(line):
    #  remove ???
    line = line.strip('? ')
    if not(line[0].isupper()):
        print_error("comment doesn't start with upper case")


def check_last_line(line):
    if line[-1] not in ".;?)":
        print_error("comment ends with '" + line[-1] + "' instead of dot")


def check_comment(strlist):
    if len(strlist) <= 1:
        return
    first_line = strlist[0].strip('- ')
    # filter copyright comment
    if first_line.startswith("Copyright"):
        return
    if first_line.startswith("gnat2why is  free  software"):
        return
    check_first_line(first_line)
    check_last_line(strlist[-1])


def check_file(fn):
    global linecount
    global cur_file
    linecount = 1
    cur_comment = []
    cur_file = fn
    with open(fn, 'r') as f:
        lines = f.readlines()
        for line in lines:
            line = line.strip()
            if is_empty_line(line):
                check_comment(cur_comment)
                cur_comment = []
            elif is_comment_line(line):
                cur_comment.append(line)
            else:
                check_comment(cur_comment)
                cur_comment = []
            linecount += 1


def main():
    for fn in check_list:
        check_file(fn)


main()
