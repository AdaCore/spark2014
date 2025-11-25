#!/usr/bin/env python3
from abc import abstractmethod
import argparse
import glob
import os
import os.path
import shutil
import sys
import yaml

descr = """Recreate the session info of a test."""


def parse_options():
    args = None
    parser = argparse.ArgumentParser(description=descr)
    parser.add_argument(
        "-j",
        dest="procs",
        type=int,
        help="Number of cores to use to recreate session (default: all)",
        default=0,
    )
    args = parser.parse_args()
    return args


cmdline_args = parse_options()

# we are assuming to be called from test dir
curdir = os.getcwd()
libdir = os.path.join(os.path.dirname(os.path.dirname(curdir)), "lib", "python")
sys.path.append(libdir)

if os.path.isfile("test.py"):
    sys.path.insert(0, curdir)
    import test  # noqa this import needs the above changes to sys.path
else:
    import test_support  # noqa import only needed in this case

# The import of test changes the directory (!), change it back
os.chdir(curdir)


class SessionGenerator:
    @abstractmethod
    def recreate_session(self):
        raise NotImplementedError

    @property
    @abstractmethod
    def contains_manual_proof(self):
        raise NotImplementedError

    def missing_contains_manual_proof_error(self):
        print(
            """test should define variable 'contains_manual_proof'"""
            """ in order to be replayed"""
        )
        exit(1)


class PythonGenerator(SessionGenerator):
    def __init__(self):
        if not hasattr(test, "contains_manual_proof"):
            self.missing_contains_manual_proof_error()
        if not hasattr(test, "replay"):
            print(
                """test should define function 'replay'"""
                """ in order to be replayed"""
            )
            exit(1)

    @property
    def contains_manual_proof(self):
        return test.contains_manual_proof

    def recreate_session(self):
        test.replay()


class YamlGenerator(SessionGenerator):
    def __init__(self, yaml):
        global cmdline_args
        if "prove_all" not in yaml:
            self.args = {}
        self.args = yaml["prove_all"]
        if "session_opt" in yaml:
            self.args.update(yaml["session_opt"])
        if "contains_manual_proof" not in yaml:
            self._contains_manual_proof = False
        else:
            self._contains_manual_proof = yaml["contains_manual_proof"]
        if "replay" not in yaml or not yaml["replay"]:
            print("replay not set in test.yaml, session generation skipped")
            exit(1)
        self.args["procs"] = cmdline_args.procs

    @property
    def contains_manual_proof(self):
        return self._contains_manual_proof

    def recreate_session(self):
        test_support.prove_all(**self.args)


def configure_test():
    if os.path.isfile("test.py"):
        return PythonGenerator()
    with open("test.yaml", "r") as f:
        data = yaml.safe_load(f)
    return YamlGenerator(data)


replayer = configure_test()


def delete(fn, isdir=False):
    testfun = os.path.isdir if isdir else os.path.isfile
    delfun = shutil.rmtree if isdir else os.remove
    print(f'  {fn}{" folder" if isdir else ""}:', end="")
    if testfun(fn):
        delfun(fn)
        print(" deleted")
    else:
        print(" not found")


if replayer.contains_manual_proof is False:
    print("""deleting subdir "proof/sessions" """)
    path = os.path.join(curdir, "proof", "sessions")
    shutil.rmtree(path, ignore_errors=True)

print("running gnatprove to rebuild sessions")
replayer.recreate_session()

print("-----------")
print("Cleanup after session regeneration:")
count = 0
for shape_file in glob.glob("proof/sessions/*/why3shapes*"):
    os.remove(shape_file)
    count += 1
print(f'  shapefiles: {"deleted" if count > 0 else "not found"}')
delete("sparklib.gpr")
for leftover in ["gnatprove", "sparklib_obj", "obj", "lib", "include"]:
    delete(leftover, isdir=True)
