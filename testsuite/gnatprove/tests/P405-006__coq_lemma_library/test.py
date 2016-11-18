from test_support import *
from gnatpython.env import putenv
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
            replace_spark_mode (new_f, False)

def copy_proof_files():
    proof_dir = os.path.join(spark_install_path(), 'lib', 'gnat', 'proof')
    shutil.copytree(proof_dir, 'proof')

# b = true => change to off
# b = false => change to on
def replace_spark_mode(fname, b):
    temp = fname + "___tmp.tmp"
    with open(temp, 'w') as new:
        with open (fname) as f:
            for lines in f:
                if b:
                    new.write (lines.replace ("SPARK_Mode => On -- TEST_ON", "SPARK_Mode => Off -- TEST_ON"))
                else:
                    new.write (lines.replace ("SPARK_Mode => Off -- TEST_ON", "SPARK_Mode => On -- TEST_ON"))
    os.remove (fname);
    shutil.move (temp, fname)

def replace_all_spark_mode (b):
    cur_dir = os.getcwd()
    lemma_files = glob.glob(os.path.join(cur_dir, '*.ad?'))
    for f in lemma_files:
        curdir = os.getcwd()
        for f in lemma_files:
            replace_spark_mode (f, b)


copy_project_file()
copy_lemma_files()
copy_proof_files()
putenv("SPARK_LEMMAS_OBJECT_DIR", "obj")
putenv("SPARK_LEMMAS_BODY_MODE", "On")
putenv("SPARK_LEMMAS_INSTALLED", "False")
prove_all(opt=["--prover=cvc4"], counterexample=False)
