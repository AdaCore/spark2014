.. index:: SPARK_Mode
.. index:: GNATmetric

The goal of reaching this level is to identify as much code as possible as
belonging to the SPARK subset. The user is responsible for identifying
candidate SPARK code by applying the marker ``SPARK_Mode`` to flag SPARK code
to GNATprove, which is responsible for checking that the code marked with
``SPARK_Mode`` is indeed valid SPARK code. Note that valid SPARK code may still
be incorrect in many ways, such as raising run-time exceptions. Being valid
merely means that the code respects the legality rules that define the SPARK
subset in the SPARK Reference Manual (see
http://docs.adacore.com/spark2014-docs/html/lrm/). The number of lines of SPARK
code in a program can be computed (along with other metrics such as the total
number of lines of code) by the metrics computation tool GNATmetric.

.. rubric:: Benefits

The stricter SPARK rules are enforced on a (hopefully) large part of the
program, which leads to higher quality and maintainability, as error-prone
features such as side effects in regular functions are avoided, and others,
such as pointers, are restricted to avoid common mistakes.
Individual and peer review processes can be reduced on the SPARK
parts of the program, since analysis automatically eliminates some categories
of defects. The parts of the program that don't respect the SPARK rules are
carefully isolated so they can be more thoroughly reviewed and tested.

.. rubric:: Impact on Process

After the initial pass of applying the SPARK rules to the program, ongoing
maintenance of SPARK code is similar to ongoing maintenance of Ada code, with a
few additional rules, such as the need to avoid side effects in
functions. These additional rules are checked automatically by running
GNATprove on the modified program, which can be done either by the developer
before committing changes or by an automatic system (continuous builder,
regression testsuite, etc.)

.. rubric:: Costs and Limitations

Pointer-heavy code needs to be rewritten to follow the ownership policy or to
hide pointers from SPARK analysis, which may be difficult. The initial pass may
require large, but shallow, rewrites in order to transform the code, for
example to annotate functions with side effects with aspect ``Side_Effects``
and move calls to such functions to the right-hand side of assignments.
