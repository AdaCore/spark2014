---
name: test-creator
description: Use this skill when creating new automated tests in this repository. It contains details about test selection, test structure, required setup, and validation steps.
---

# Test Creator

## Purpose

The purpose of this skill is to add a new test in the testsuite/gnatprove/tests subfolder.

## Inputs

The expected test behavior, or tool behavior under test, or code to be covered should be available.

## Workflow

1. Create the test folder under testsuite/gnatprove/tests, see `Test naming` below
2. Add the test files, except for expected output
3. Generate the current output using ./run-tests <testname> --rewrite, or using ./update-expected-outputs
   if the testsuite was already run previously
4. Verify that the current output is expected (visual inspection)

TODO: Document the step-by-step process for choosing where tests belong, implementing them, and verifying them.

## Repository Conventions

### Test naming

Tests have the form `<gitlab_issue_id>__<description>`, for example `128__type_invariants. You should have enough
context to suggest a description, but you probably need to ask the user about the gitlab issue id.

### Resources

The testsuite heavily uses the `test_support.py` file in testsuite/gnatprove/lib/python. See details below.

### Test structure

#### Yaml tests

The simplest test setup is simply one or multiple Ada sources, with a test.out file which contains the expected output.

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

This is the preferred form of writing a test, if possible. Only write a .yaml file if needed.

#### Python tests

In case a simple invocation of `prove_all` or `do_flow` is not enough, a `test.py` can be added to the
test folder. The prove_all/do_flow entries of the .yaml file are ignored in that case.

Python tests are to be used if the tool is to be run multiple times, or other tools (not gnatprove) should be
run, or if output needs to be processed in some way.

#### Replay tests

TODO


## Validation

Always run `./run-tests <testname>` in testsuite/gnatprove to validate that the newly added test passes.
