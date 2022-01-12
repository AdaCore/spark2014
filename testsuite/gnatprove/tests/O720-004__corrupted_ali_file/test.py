from test_support import *
import os
import time


# this test corrupts an ALI file and checks that gnatprove detects the issue.

last_line = ''


def truncate_four_lines(a):
    global last_line
    statinfo = os.stat(a)
    with open(a,"r") as f:
        content = f.readlines()
    last_line = content[-1]
    content = content[:-4]
    with open(a,"w") as f:
        for line in content:
            f.write(line)
    os.utime(a, (statinfo.st_atime, statinfo.st_mtime))


target_ali = os.path.join("gnatprove", "phase1", "test.ali")

prove_all()
print("------------------")
truncate_four_lines(target_ali)
prove_all()

with open(target_ali, "r") as f:
    content = f.readlines()
    if last_line != content[-1]:
        print("Wrong last line")
        print(content[-1])
