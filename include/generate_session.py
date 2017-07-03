import os
import shutil
import difflib


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
                    new.write(
                        line.replace("SPARK_Mode => On -- TEST_ON", "SPARK\
_Mode => Off -- TEST_ON"))
                else:
                    new.write(
                        line.replace("SPARK_Mode => Off -- TEST_ON", "SPARK\
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


def copy_file(f_ctx, f_v):
    # This creates a new file which is the new .ctx file.
    # Behavior: Before the intros tactic we append only f_v; after the intros
    # or '#' character, we append only f_ctx.
    temp = f_ctx + "___tmp.tmp"
    b = False
    with open(temp, 'w') as new_temp:
        with open(f_v) as file_v:
            for line in file_v:
                if line[:6] == "intros":
                    break
                else:
                    new_temp.write(line)
        with open(f_ctx) as file_ctx:
            for line in file_ctx:
                if line[:6] == "intros" or line[:1] == "#":
                    b = True
                if b:
                    new_temp.write(line)
#   Replace context file with the temp file
    os.remove(f_ctx)
    shutil.move(temp, f_ctx)


def diff_file(f_ctx, g_v):
    # This function makes a diff without spaces between files f and g. If there
    # is a line which is in the first file and not in the second one, create a
    # temp diff file of same name in folder temp, otherwise do not create temp
    # file.
    # We assume f ends with .ctx and g ends with .v. Basically, don't use this
    # function anywhere else.
    diff_seen = False
    with open(f_ctx, 'r') as file1:
        with open(g_v, 'r') as file2:
            # Removing spaces because cpp introduce extra spaces as diff.
            lines1 = map(lambda y:
                         filter(lambda x:
                                x not in ' \t', y), file1.readlines())
            lines2 = map(lambda y:
                         filter(lambda x:
                                x not in ' \t', y), file2.readlines())
            diff = difflib.unified_diff(
                lines1,
                lines2,
                fromfile=f_ctx,
                tofile=g_v, n=1)
            for line in diff:
                if not line[0] == '-':
                    diff_seen = True
                    break
    if diff_seen:
        temp_file = os.path.basename(f_ctx)[:-4] + ".diff"
        temp_path = os.path.join("./temp", temp_file)
        with open(temp_path, 'a') as new:
            for line in diff:
                new.write(line)


def diff_all(gen_ctx):
    # If files have changed due to changes in spark/why3 generates files,
    # diff will be printed in temp.
    # For technical reasons, diff are printed without spaces
    # Do not use this function in an other context. It is used only once
    # with gen_ctx to False meaning files are not erased and replaced with
    # new ones. To replace them, pass True.
    for root, dirs, files in os.walk('./proof'):
        for name in files:
            if name.endswith(".v"):
                ctx_file = os.path.join(root, name[:-2] + ".ctx")
                v_file = os.path.join(root, name)
                diff_file(ctx_file, v_file)
                if gen_ctx:
                    copy_file(ctx_file, v_file)


def kill_and_regenerate_all():
    change_all_spark_mode(False)
    if os.path.isdir("./proof/sessions"):
        print("The folder proof/sessions still exists.")
        print("Please, move it to be able to regenerate session.")
        exit(1)
    if os.path.isdir("./temp"):
        print("The folder temp will be used. Please move it.")
        exit(1)
    else:
        os.makedirs("./temp")
    os.system("make clean")
#   Force regeneration of coq files where necessary.
#   This step is used to generate the fake coq files and put the names of
#   coq files inside the session. This cannot be done in one step because
#   if coq files are already present, it will create new ones (not
#   check the present coq files).
    with open("manual_proof.in") as f:
        for i in f:
            exec_gnatprove(i)
#   Make the diff between generated .v and .ctx files. If there are differences
#   between them not in the proof, you are sure to fail
    diff_all(False)
#   cleaning and regeneration of *.v
    os.system("make clean")
    os.system("make generate")
    os.system("gnatprove -P spark_lemmas.gpr --prover=cvc4 \
--level=1 --no-counterexample -j0")
#   Do *not* remove this call as it is used to check that coq proofs are
#   correct after regeneration. And ability to generate session is *necessary*
#   as there is no way to extend a session in gnatprove.
    with open("manual_proof.in") as v:
        for i in v:
            exec_gnatprove(i)
    exec_cvc4 = "gnatprove -P spark_lemmas.gpr --prover=cvc4 \
--level=4 --no-counterexample -j0"
    exec_z3 = "gnatprove -P spark_lemmas.gpr --prover=z3 \
--level=2 --no-counterexample -j0"
    exec_altergo_report = "gnatprove -P spark_lemmas.gpr --report=statistics \
--prover=alt-ergo --level=4 --no-counterexample -j0"
    print (exec_cvc4)
    os.system(exec_cvc4)
#   discharge the remaining proofs with z3 and alt-ergo
    print (exec_z3)
    os.system(exec_z3)
    print (exec_altergo_report)
    os.system(exec_altergo_report)
    change_all_spark_mode(True)

kill_and_regenerate_all()
