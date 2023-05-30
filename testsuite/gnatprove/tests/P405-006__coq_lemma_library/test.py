from test_support import prove_all, spark_install_path
from glob import glob
import os

import shutil


def copy_project_file():
    libraries_gpr = os.path.join(spark_install_path(), "lib", "gnat", "sparklib.gpr")
    shutil.copyfile(libraries_gpr, "sparklib.gpr")


def copy_lemma_files():
    include_dir = os.path.join(spark_install_path(), "include", "spark")
    lemma_files = glob(os.path.join(include_dir, "*.ad?"))
    for f in lemma_files:
        curdir = os.getcwd()
        for f in lemma_files:
            new_f = os.path.join(curdir, os.path.basename(f))
            shutil.copyfile(f, new_f)


def copy_proof_files():
    proof_dir = os.path.join(spark_install_path(), "lib", "gnat", "proof")
    shutil.copytree(proof_dir, "proof")


copy_project_file()
copy_lemma_files()
copy_proof_files()
os.environ["SPARKLIB_OBJECT_DIR"] = "obj"
os.environ["SPARKLIB_BODY_MODE"] = "On"
os.environ["SPARKLIB_INSTALLED"] = "False"

prove_all(
    replay=True,
    prover=["coq", "cvc5", "z3", "altergo", "colibri"],
    counterexample=False,
    #  We need to remove useless coq warning for Grammar extension
    filter_output=".*Grammar extension",
    filter_sparklib=False,
)
