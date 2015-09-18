from test_support import *
from time import sleep
import os.path

#this test corrupts an ALI file and checks that gnatprove detects the issue.

target_ali = os.path.join("gnatprove", "test.ali")

def truncate_four_lines(a):
    with open(a,"r") as f:
        content = f.readlines()
    content = content[:-4]
    with open(a,"w") as f:
        for line in content:
            f.write(line + '\n')

prove_all()
sleep(4)
truncate_four_lines(target_ali)
prove_all()


