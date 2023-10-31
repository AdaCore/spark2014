The goal of reaching this level is to make sure that no uninitialized data can
ever be read and, optionally, to prevent unintended access to global
variables. This also ensures no possible interference between parameters and
global variables; i.e., the same variable isn't passed multiple times to a
subprogram, either as a parameter or global variable. Finally, it ensures that
functions must return in the absence of run-time error.

.. rubric:: Benefits

The SPARK code is guaranteed to be free from a number of defects: no reads of
uninitialized variables, no possible interference between parameters and global
variables, no unintended access to global variables, no infinite loop or
recursion in functions.

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

The guarantees offered at Bronze level do not extend to subprograms with the
annotation ``Skip_Flow_And_Proof``, which are only analyzed at Stone
level. These guarantees also do not extend to code in the following constructs:

* branches ending in an error-signaling statement such as ``pragma Assert
  (False)``, which flow analysis treats as dead code.
* exception handlers and any code that can be executed after catching an
  exception, which flow analysis could treat as dead code if no callee has a
  corresponding exceptional contract.

Analysis by proof at :ref:`Silver Level <Silver Level>` and above is required
in these two cases.

The property that no uninitialized data can be read can only be guaranteed when
the following SPARK feature is not used, as its purpose is precisely to allow
more complex initialization patterns that can only be analyzed by proof at
:ref:`Silver Level <Silver Level>` and above:

* relaxed initialization of types and variables using aspect
  ``Relaxed_Initialization``.

The property that functions must return in the absence of run-time errors can
only be guaranteed when the following SPARK features are not used, as their
purpose is precisely to allow more complex termination conditions that can only
be analyzed by proof at :ref:`Silver Level <Silver Level>` and above:

* specification of termination with aspect ``Always_Terminate`` with a
  non-static expression;
* specification of subprogram variants with aspect ``Subprogram_Variant``;
* specification of loop variants with pragma ``Loop_Variant``;
* specification of exceptional contracts with aspect ``Exceptional_Cases``.

.. index:: False alarm

The initial pass may require a substantial effort to deal with the false
alarms, depending on the coding style adopted up to that point. The analysis
may take a long time, up to an hour on large programs, but it is guaranteed to
terminate. Flow analysis is, by construction, limited to local understanding of
the code, with no knowledge of values (only code paths) and handling of
composite variables is only through calls, rather than component by component,
which may lead to false alarms.
