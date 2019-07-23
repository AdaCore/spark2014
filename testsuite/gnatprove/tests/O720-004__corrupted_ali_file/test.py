from test_support import *
import os
import time

#this test corrupts an ALI file and checks that gnatprove detects the issue.

target_ali = os.path.join("gnatprove", "phase1", "test.ali")

def truncate_four_lines(a):
    statinfo = os.stat(target_ali)
    with open(a,"r") as f:
        content = f.readlines()
    content = content[:-4]
    with open(a,"w") as f:
        for line in content:
            f.write(line)
    os.utime(target_ali, (statinfo.st_atime, statinfo.st_mtime))

prove_all()
truncate_four_lines(target_ali)
prove_all()
