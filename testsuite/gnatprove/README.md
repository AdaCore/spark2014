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
equal to the test name.

By default, a test just contains Ada sources and an expected output in the
`test.out` file. In this case, the test driver runs the python function
`prove_all()`, or `do_flow()` if the test directory name contains the `__flow`
substring. Both functions are defined in the helper library in
`lib/python/test_support.py`.  Arguments to this call can be provided via a
`test.yaml` file in the test directory, in the following form:

```
prove_all:
  steps: 100
  prover: ["cvc4"]
  ...
```

The term `prove_all` above must be replaced by `do_flow` in the case of a test
that contains `__flow`. The keys are identical to the named parameters of the
corresponding python functions, see those functions for more information.

This default behavior can be overridden by placing a `test.py` file in the test
directory. In that case the test simply runs that test.py file.
`prove_all/do_flow` entries in the .yaml file are ignored in this case.

The `test.yaml` file can contain a field `large` like this:

```
large: True
```

If set to true, the test is considered "large" and is skipped by default,
unless the `large` discriminant is provided. If omitted, `large` is assumed to
be `False`.

Another field is the `timeout` field:
```
timeout: 1500
```
This directive replaces the default timeout of 300s (5 minutes) for this test.
