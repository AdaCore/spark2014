#!/usr/bin/python3

import os.path
import re
import sys

# stop looking for copyright after this number of lines
max_copyright_lines = 30

# expected width of copyright comment
expected_length = 78

# current year
current_year = 2025

box_copyright_line_regex = re.compile(
    r"--.*Copyright \(C\) (\d\d\d\d)(-\d\d\d\d)?,(.*)--"
)

line_copyright_line_regex = re.compile(
    r"(--.*Copyright \(C\) )(\d\d\d\d)(-\d\d\d\d)?(,.*)"
)

matched = False


def process_line(line):
    global matched
    m = box_copyright_line_regex.match(line)
    if m:
        matched = True
        year = m.group(1)
        name = m.group(3).strip()
        used_chars = 25 + 4 + len(name)
        free_chars = expected_length - used_chars
        first_fill = " " * (free_chars // 2 + free_chars % 2)
        last_fill = " " * (free_chars // 2)
        line = (
            f"--{first_fill}Copyright (C) {year}-{current_year}, "
            f"{name}{last_fill}--\n"
        )
        return line
    else:
        m = line_copyright_line_regex.match(line)
        if m:
            matched = True
            prelude = m.group(1)
            year = m.group(2)
            name = m.group(4)
            line = f"{prelude}{year}-{current_year}{name}\n"
            return line
        else:
            return line


def process_file(fn):
    print("processing " + fn)
    global matched
    matched = False
    with open(fn, "r+") as f:
        lines = f.readlines()
        f.seek(0)
        count = 0
        for line in lines:
            count += 1
            if count <= max_copyright_lines:
                line = process_line(line)
            f.write(line)
        f.truncate()
    if not matched:
        print("did not rewrite anything in " + fn)


def in_files(dir):
    for root, _dirs, files in os.walk(dir):
        for f in files:
            ext = os.path.splitext(f)[1]
            if ext in (".ads", ".adb", ".c", ".h"):
                name = os.path.join(root, f)
                process_file(name)


def main():
    for x in range(1, len(sys.argv)):
        if os.path.isdir(sys.argv[x]):
            in_files(sys.argv[x])
        else:
            process_file(sys.argv[x])


main()
