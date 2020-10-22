Contents
========

This directory contains the testsuite for SPARK 2014.

Requirements
============

Python >= 3.7
e3-testsuite via `pip install` or from
[github](https://github.com/AdaCore/e3-testsuite).

Running the testsuite
=====================

Simply run
```
./run-tests
```

You can add the `--help` switch to see other options.

Test structure
==============

Each subdirectory of `tests` is a separate testcase, the directory name is
equal to the test name. The `test.py` file (if present) contains the test
script to be run. This test script generally uses some functions from the
Python library in `lib/python`.

If the `test.py` is missing, a default test script is assumed. If the test name
contains "__flow" as a substring, the default test script runs the `do_flow()`
function with no arguments, otherwise it runs `prove_all()`.
