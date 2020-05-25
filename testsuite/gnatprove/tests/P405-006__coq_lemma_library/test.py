from test_support import *
import os

import shutil

def copy_project_file():
    lemma_gpr = os.path.join(spark_install_path(), 'lib', 'gnat', 'spark_lemmas.gpr')
    shutil.copyfile(lemma_gpr, 'spark_lemmas.gpr')

def copy_lemma_files():
    include_dir = os.path.join(spark_install_path(), 'include', 'spark')
    lemma_files = glob.glob(os.path.join(include_dir, '*.ad?'))
    for f in lemma_files:
        curdir = os.getcwd()
        for f in lemma_files:
            new_f = os.path.join(curdir, os.path.basename(f))
            shutil.copyfile(f, new_f)

def copy_proof_files():
    proof_dir = os.path.join(spark_install_path(), 'lib', 'gnat', 'proof')
    shutil.copytree(proof_dir, 'proof')

copy_project_file()
copy_lemma_files()
copy_proof_files()
os.environ["SPARK_LEMMAS_OBJECT_DIR"] = "obj"
os.environ["SPARK_LEMMAS_BODY_MODE"] = "On"
os.environ["SPARK_LEMMAS_INSTALLED"] = "False"

prove_all(opt=["--replay"],
          prover = ["coq","cvc4","z3","altergo"],
          counterexample=False,
          #  We need to remove useless coq warning for Grammar extension
          filter_output=".*Grammar extension")
