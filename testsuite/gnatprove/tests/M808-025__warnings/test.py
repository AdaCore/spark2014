from test_support import check_output_file, clean, prove_all


def cmd_line_or_ide_mode(opt=None):
    if opt is None:
        opt = []
    print("Do not stop at compilation:")
    print("---------------------------")
    prove_all(opt=opt + ["-cargs", "-gnatwae"], exit_status=0)
    clean()

    print("")
    print(
        (
            "Do not issue all compilation warnings,"
            " stop at flow warnings treated as errors:"
        )
    )
    print(
        "---------------------------------------"
        "----------------------------------------"
    )
    prove_all(opt=opt + ["--warnings=error", "-cargs", "-gnatwa"], exit_status=1)
    clean()

    print("")
    print(
        (
            "Do not issue all compilation warnings,"
            " stop at flow warnings treated as errors:"
        )
    )
    print(
        "---------------------------------------"
        "----------------------------------------"
    )
    prove_all(opt=opt + ["--warnings=error"], exit_status=1)
    clean()

    print("")
    print(
        "Do not issue any compilation warnings, "
        "stop at flow warnings treated as errors:"
    )
    print(
        "----------------------------------------"
        "---------------------------------------"
    )
    prove_all(opt=opt + ["--warnings=error", "-cargs", "-gnatws"], exit_status=1)
    clean()

    print("")
    print("Do not issue all compilation warnings, issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt + ["--warnings=continue", "-cargs", "-gnatwa"], exit_status=0)
    clean()

    print("")
    print("Do not issue all compilation warnings, " "issue flow warnings and continue:")
    print("----------------------------------" "--------------------------------------")
    prove_all(opt=opt + ["--warnings=continue"], exit_status=0)
    clean()

    print("")
    print("Do not issue any compilation warnings, issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt + ["--warnings=continue", "-cargs", "-gnatws"], exit_status=0)
    clean()

    print("")
    print("Issue all compilation warnings, do not issue flow warnings and continue:")
    print("------------------------------------------------------------------------")
    prove_all(opt=opt + ["--warnings=off", "-cargs", "-gnatwa"], exit_status=0)
    clean()

    print("")
    print(
        "Do not issue all compilation warnings, "
        "do not issue flow warnings and continue:"
    )
    print(
        "--------------------------------------"
        "-----------------------------------------"
    )
    prove_all(opt=opt + ["--warnings=off"], exit_status=0)
    clean()

    print("")
    print(
        "Do not issue any compilation warnings, "
        "do not issue flow warnings and continue:"
    )
    print(
        "---------------------------------------"
        "----------------------------------------"
    )
    prove_all(opt=opt + ["--warnings=off", "-cargs", "-gnatws"], exit_status=0)
    clean()


cmd_line_or_ide_mode()
print("")
cmd_line_or_ide_mode(opt=["--ide-progress-bar"])
print("")
prove_all(exit_status=0)
print("")
check_output_file()
