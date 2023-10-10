The goal of reaching this level is to make sure that no uninitialized data can
ever be read and, optionally, to prevent unintended access to global
variables. This also ensures no possible interference between parameters and
global variables; i.e., the same variable isn't passed multiple times to a
subprogram, either as a parameter or global variable.

.. rubric:: Benefits

The SPARK code is guaranteed to be free from a number of defects: no reads of
uninitialized variables, no possible interference between parameters and global
variables, no unintended access to global variables.

.. index:: Global; for Bronze level

When ``Global`` contracts are used to specify which global variables are read
and/or written by subprograms, maintenance is facilitated by a clear
documentation of intent. This is checked automatically by GNATprove, so that
any mismatch between the implementation and the specification is reported.

.. rubric:: Impact on Process

An initial pass is required where flow analysis is enabled and the resulting
messages are resolved either by rewriting code or justifying any false
alarms. Once this is complete, ongoing maintenance can preserve the same
guarantees at a low cost. A few simple idioms can be used to avoid most false
alarms, and the remaining false alarms can be easily justified.

.. rubric:: Costs and Limitations

.. index:: False alarm

The initial pass may require a substantial effort to deal with the false
alarms, depending on the coding style adopted up to that point. The analysis
may take a long time, up to an hour on large programs, but it is guaranteed to
terminate. Flow analysis is, by construction, limited to local understanding of
the code, with no knowledge of values (only code paths) and handling of
composite variables is only through calls, rather than component by component,
which may lead to false alarms.
