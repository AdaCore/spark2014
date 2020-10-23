#!/usr/bin/env python

import os
import shutil
import difflib
import sys


def run(cmd):
    print("")
    print("run: " + cmd)
    os.system(cmd)


def run_manual(check_to_prove, option=""):
    cmd = "gnatprove -P spark_lemmas.gpr -U --prover=coq"
    if ":" not in check_to_prove:
        run(cmd + " " + option + check_to_prove)
    else:
        run(cmd + " " + option + "--limit-line=" + check_to_prove)


def run_automatic(prover, level=4):
    cmd = "gnatprove -P spark_lemmas.gpr --no-counterexample -j0" + \
          " --prover=" + prover + " --level=" + str(level)
    run(cmd)


def run_automatic_timeout(prover, level=4, timeout=100):
    cmd = "gnatprove -P spark_lemmas.gpr --no-counterexample -j0" + \
          " --prover=" + prover + " --level=" + str(level) + \
          " --timeout=" + str(timeout)
    run(cmd)


def run_options(opt):
    cmd = "gnatprove -P spark_lemmas.gpr --no-counterexample -j0 " + opt
    run(cmd)


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
            lines1 = list(map(lambda y:
                              str(filter(lambda x:
                                         x not in ' \t', y)),
                              file1.readlines()))
            lines2 = list(map(lambda y:
                              str(filter(lambda x:
                                         x not in ' \t', y)),
                              file2.readlines()))
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


def kill_and_regenerate(check):
    list_of_check = []
    if check:
        list_of_check.append(check)
    else:
        with open("manual_proof.in") as f:
            for i in f:
                list_of_check.append(i)
    print("")
    print("--------------------------")
    print("Cleanup previous artifacts")
    print("--------------------------")
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
    print("")
    print("----------------------------")
    print("Generate the Coq proof files")
    print("----------------------------")
#   Force regeneration of coq files where necessary.
#   This step is used to generate the fake coq files and put the names of
#   coq files inside the session. This cannot be done in one step because
#   if coq files are already present, it will create new ones (not
#   check the present coq files).
    for i in list_of_check:
        run_manual(i)
#   Make the diff between generated .v and .ctx files. If there are differences
#   between them not in the proof, you are sure to fail
    diff_all(False)
    print("")
    print("-----------------------------")
    print("Check and register Coq proofs")
    print("-----------------------------")
#   cleaning and regeneration of *.v
    os.system("make clean")
    os.system("make generate")
    run_automatic("cvc4", level=1)
#   Do *not* remove this call as it is used to check that coq proofs are
#   correct after regeneration. And ability to generate session is *necessary*
#   as there is no way to extend a session in gnatprove.
    for i in list_of_check:
        run_manual(i)
    print("")
    print("---------------------------------------------")
    print("Prove remaining checks with automatic provers")
    print("---------------------------------------------")
    print("")
    print("---------------")
    print("Start with CVC4")
    print("---------------")
    run_automatic("cvc4", level=2)
    print("")
    print("------------")
    print("Then with Z3")
    print("------------")
    run_automatic_timeout("z3", level=2, timeout=100)
    print("")
    print("-----------------")
    print("End with Alt-Ergo")
    print("-----------------")
    run_automatic_timeout("altergo", level=2)
    print("")
    print("---------------------------")
    print("Summarize all proved checks")
    print("---------------------------")
    run_options(opt="--output-msg-only --report=provers")


def choose_mode():
    if len(sys.argv) == 1:
        kill_and_regenerate(None)
    else:
        if len(sys.argv) == 2:
            kill_and_regenerate(sys.argv[1])


choose_mode()
