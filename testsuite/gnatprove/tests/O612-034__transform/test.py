from test_support import *
import os.path
import shutil
import time

# This test tests the capacity of gnatprove to follow transformations that
# have been inserted into the Why3 session

session_file = os.path.join('gnatprove', 'test__p', 'why3session.xml')

def print_session_proofs():
    with open(session_file) as f:
        content = f.readlines()
        proof = grep(".*proof.*", content)
        print(len(proof))

# run gnatprove once
prove_all(cache_allowed=False)
# touch file so that rerunning gnatprove will re-run the proof machinery
touch('test.adb')
# print the number of proofs in the session
print_session_proofs()
# copy a file which has an extra transformation applied to the unique goal
shutil.copyfile('new.xml', session_file)
sleep(4)
# run gnatprove again and print number of proofs, should be higher now
prove_all(cache_allowed=False)
print_session_proofs()
