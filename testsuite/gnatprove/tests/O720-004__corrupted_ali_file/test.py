from test_support import *
import os
import time

#this test corrupts an ALI file and checks that gnatprove detects the issue.

def truncate_four_lines(a):
    statinfo = os.stat(a)
    with open(a,"r") as f:
        content = f.readlines()
    content = content[:-4]
    with open(a,"w") as f:
        for line in content:
            f.write(line)
    os.utime(a, (statinfo.st_atime, statinfo.st_mtime))

target_ali = os.path.join("gnatprove", "phase1", "test.ali")

prove_all()
truncate_four_lines(target_ali)
prove_all()
