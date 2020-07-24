Contents
========

This folder contains the code examples used and referenced in the SPARK UG.
Each example is in a standalone subfolder of the "tests" folder. The output for
each example is in the "test.out" file of the test.

Usage
=====

Just run `run_examples.py` to run SPARK on all examples and regenerate the
output. Add an example name or pattern to run a subset of the examples.

Nightly Source packaging
========================

During source packaging in the nightly builds, the output for the examples is
regenerated, and if diffs exist, they are submitted via git review.


How to add a Code example
=========================

Create a new subdirectory of the "tests" folder. Then put the Ada/SPARK files
there as well as exactly one project file. Finally, create an empty `test.out`
file. Running the example using `run_examples.py` will update the `test.out`
file with the current output of the tool.
