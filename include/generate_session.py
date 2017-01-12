import os
import shutil


def exec_gnatprove(file_to_prove, option=""):
    cmd = "gnatprove -P spark_lemmas.gpr -U --prover=coq"
    if ":" not in file_to_prove:
        print (cmd + " " + option + file_to_prove)
        os.system(cmd + " " + option + file_to_prove)
    else:
        print (cmd + " " + option + "--limit-line=" + file_to_prove)
        os.system(cmd + " " + option + "--limit-line=" + file_to_prove)


def check_all(f):
    for i in f:
        exec_gnatprove(i)
    os.system("gnatprove -P spark_lemmas.gpr --prover=cvc4 --level=2\
 --no-counterexample -j0")


# b = true => change to off
# b = false => change to on
def replace_spark_mode(fname, b):
    temp = fname + "___tmp.tmp"
    with open(temp, 'w') as new:
        with open(fname) as f:
            for line in f:
                if b:
                    new.write(line.replace("SPARK_Mode => On -- TEST_ON", "SPARK\
_Mode => Off -- TEST_ON"))
                else:
                    new.write(line.replace("SPARK_Mode => Off -- TEST_ON", "SPARK\
_Mode => On -- TEST_ON"))
    os.remove(fname)
    shutil.move(temp, fname)


# This changes the spark_mode in lines tagged with -- TEST_ON in commentary
# true => change to off
# false => change to on
def change_all_spark_mode(b):
    for files in os.listdir('.'):
        if files.endswith(".adb"):
            replace_spark_mode(files, b)


def kill_and_regenerate_all():
    change_all_spark_mode(False)
    os.system("make clean")
#   Force regeneration of coq files where necessary.
#   This step is used to generate the fake coq files and put the names of
#   coq files inside the session. This cannot be done in one step because
#   if coq files are already present, it will create new ones (not
#   check the present coq files).
    with open("manual_proof.in") as f:
        for i in f:
            exec_gnatprove(i)
#   cleaning and regeneration of *.v
    os.system("make clean")
    os.system("make generate")
    with open("manual_proof.in") as v:
        for i in v:
            exec_gnatprove(i)
    os.system("gnatprove -P spark_lemmas.gpr --prover=cvc4 \
--level=4 --no-counterexample -j0")
#   discharge the remaining proofs with z3 and alt-ergo
    os.system("gnatprove -P spark_lemmas.gpr --prover=z3 \
--level=2 --no-counterexample -j0")
    os.system("gnatprove -P spark_lemmas.gpr --report=statistics \
--prover=alt-ergo --level=4 --no-counterexample -j0")
    change_all_spark_mode(True)

kill_and_regenerate_all()
