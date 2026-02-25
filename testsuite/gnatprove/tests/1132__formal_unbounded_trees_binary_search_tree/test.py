from test_support import prove_all, sparklib_exec_test


if __name__ == "__main__":
    prove_all(sparklib=True, opt=["--no-inlining"], level=3, sparklib_bodymode=True)
    sparklib_exec_test()
