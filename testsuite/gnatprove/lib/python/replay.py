#!/usr/bin/env python3
import glob
import os
import os.path
import shutil
import sys

# we are assuming to be called from test dir
curdir = os.getcwd()
libdir = os.path.join(os.path.dirname(os.path.dirname(curdir)), "lib", "python")
sys.path.append(libdir)
sys.path.insert(0, curdir)

import test  # noqa this import needs the above changes to sys.path

# The import of test changes the directory (!), change it back
os.chdir(curdir)

if not hasattr(test, "contains_manual_proof"):
    print(
        """test should define variable 'contains_manual_proof'"""
        """ in order to be replayed"""
    )
    exit(1)
if not hasattr(test, "replay"):
    print("""test should define function 'replay'""" """ in order to be replayed""")
    exit(1)

if test.contains_manual_proof is False:
    print("""deleting subdir "proof/sessions" """)
    path = os.path.join(curdir, "proof", "sessions")
    shutil.rmtree(path, ignore_errors=True)

print("running gnatprove to rebuild sessions")
test.replay()

for shape_file in glob.glob("proof/sessions/*/why3shapes*"):
    print("deleting shapes file ", shape_file)
    os.remove(shape_file)
if os.path.isdir("gnatprove"):
    shutil.rmtree("gnatprove")
