import os.path
from test_support import *

def cmd_line_or_ide_mode(opt=[]):
    print("Stop at compilation:")
    print("--------------------")
    prove_all(opt=opt+["-cargs", "-gnatwae"])
    clean()

    print("")
    print("Issue all compilation warnings, stop at flow warnings treated as errors:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=error", "-cargs", "-gnatwa"])
    clean()

    print("")
    print("Do not issue all compilation warnings, stop at flow warnings treated as errors:")
    print("-------------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=error"])
    clean()

    print("")
    print("Do not issue any compilation warnings, stop at flow warnings treated as errors:")
    print("-------------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=error", "-cargs", "-gnatws"])
    clean()

    print("")
    print("Issue all compilation warnings, issue flow warnings and continue:")
    print("-----------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=continue", "-cargs", "-gnatwa"])
    clean()

    print("")
    print("Do not issue all compilation warnings, do not issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=continue"])
    clean()

    print("")
    print("Do not issue any compilation warnings, issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=continue", "-cargs", "-gnatws"])
    clean()

    print("")
    print("Issue all compilation warnings, do not issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=off", "-cargs", "-gnatwa"])
    clean()

    print("")
    print("Do not issue all compilation warnings, do not issue flow warnings and continue:")
    print("-------------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=off"])
    clean()

    print("")
    print("Do not issue any compilation warnings, do not issue flow warnings and continue:")
    print("-------------------------------------------------------------------------------")
    prove_all(opt=opt+["--warnings=off", "-cargs", "-gnatws"])
    clean()

cmd_line_or_ide_mode()
cmd_line_or_ide_mode(opt=["--ide-progress-bar"])
prove_all()
check_output_file()
