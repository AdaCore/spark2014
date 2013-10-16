.. _formal verification with gnatprove:

************************************
Formal Verification with |GNATprove|
************************************

The |GNATprove| tool is packaged as an executable called ``gnatprove``. Like
other tools in |GNAT Pro| Toolsuite, |GNATprove| is based on the structure of
GNAT projects, defined in ``.gpr`` files.

A crucial feature of |GNATprove| is that it interprets annotations exactly like
they are interpreted at run time during tests. In particular, their executable
semantics includes the verification of run-time checks, which can be verified
statically with |GNATprove|. |GNATprove| also performs additional verifications
on the specification of the expected behavior itself, and its correspondence to
the code.

How to Run |GNATprove|
======================

Running |GNATprove| from the Command Line
-----------------------------------------

|GNATprove| can be run from the command line as follows::

    gnatprove -P <project-file.gpr>

In the appendix, section :ref:`command line`, you can find an exhaustive list
of switches; here we only give an overview over the most common uses. Note that
|GNATprove| cannot be run without a project file.

When given a list of files, |GNATprove| will consider them as entry points of
the program and analyze these units and all units on which they depend. With
option ``-u``, the dependencies are not considered, only the given files
themselves are analyzed. With option ``-U``, all files of all projects are
analyzed.

|GNATprove| consists of two distinct analyses, flow analysis and proof. Flow
analysis checks the correctness of aspects related to data flow (``Global``,
``Depends``, ``Abstract_State``, ``Initializes``, and refinement versions of
these), and verifies the initialization of variables. Proof verifies the
absence of run-time errors and the correctness of assertions such as ``Pre``
and ``Post`` aspects.  Using the switch ``--mode=<mode>``, whose possible
values are ``flow``, ``prove`` and ``all``, you can choose to perform only one
or both of these analyses (``all`` is the default).

Using the option ``--limit-line=`` one can limit proofs to a particular file
and line of an Ada file. For example, if you want to prove only the file 12 of
file ``example.adb``, you can add the option ``--limit-line=example.adb:12`` to
the call to |GNATprove|. Using the option ``--limit-subp=`` one can limit proofs
to a subprogram declared in a particular file at a particular line.

A number of options exist to influence the behavior for proof. Internally, the
prover Alt-Ergo is called repeatedly for each check or assertion. Using the
option ``--timeout``, one can change the maximal time that is allocated to prove
each check or assertion (default: 1s). Using the option ``--steps`` (default:
not used), one can set the maximum number of reasoning steps that Alt-Ergo is
allowed to perform before giving up. The ``steps`` option should be used when
predictable results are required, because the results with a timeout may differ
depending on the computing power or current load of the machine. The option
``-j`` activates parallel compilation and parallel proofs.

The way checks are passed to Alt-Ergo can also be influenced using the option
``--proof``. By default, Alt-Ergo is invoked a single time for each check or
assertion (mode ``no_split``). This can be changed using mode ``path_wp`` to
invoke Alt-Ergo for each *path* that leads to the check. This option usually
takes much longer, because Alt-Ergo is invoked much more often, but may give
better proof results. Using mode ``all_split``, in addition, conjunctions (such
as ``and`` and ``and then``) in assertions are split and passed seperately to
Alt-Ergo. Finally, in mode ``then_split``, invoking Alt-Ergo a single time on
the entire check is tried, and only if the check is not proved, the other
techniques (splitting conjunctions and trying each path separately) are tried.

By default, |GNATprove| avoids reanalyzing unchanged files, on a
per-unit basis. This mechanism can be disabled with the option ``-f``.

By default, |GNATprove| stops at the first unit where it detect errors
(compilation errors, SPARK 2014 violations, or flow analysis errors).  The
option ``-k`` can be used to get |GNATprove| to issue errors of the same kind
for multiple units. If there are any `compilation` errors (really violations of
Ada legality rules here), |GNATprove| does not attempt analysis. If there are
violations of |SPARK| legality rules, or flow analysis errors, |GNATprove| does
not attempt proof.

.. _implementation_defined:

Implementation-Defined Behavior
-------------------------------

A |SPARK| program is guaranteed to be unambiguous, so that formal verification
of properties is possible. However, some behaviors may depend on the compiler
used. By default, |GNATprove| adopts the same choices as the GNAT
compiler. |GNATprove| also supports other compilers by providing special
switches:

* ``-gnateT`` for specifying the target configuration
* ``--pedantic`` for warning about possible implementation-defined behavior

Target Parameterization
^^^^^^^^^^^^^^^^^^^^^^^

Target parameterization consists in passing to |GNATprove| a file which defines
the parameters for the target on which the program will be run. These include
the size and alignment of standard integer types, endianness, the kinds of
floating-point numbers, etc. The format of this file should match the format of
the file generated by calling |GNAT Pro| with switch ``-gnatet``.

Target parameterization can be used:

* to specify a target different than the host on which |GNATprove| is run, when
  cross-compilation is used. If |GNAT Pro| is the cross compiler, the
  configuration file can be generated by calling it with the switch
  ``-gnatet=?``. Otherwise, the target file should be generated manually.
* to specify the parameters for a different compiler than |GNAT Pro|, even when
  the host and target are the same. In that case, the target file should be
  generated manually.

Parenthesized Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In Ada, non-parenthesized arithmetic operations could be re-ordered by the
compiler, which may result in a failing computation (due to overflow checking)
becoming a successful one, and vice-versa. By default, |GNATprove| evaluates
all expressions left-to-right, like GNAT. When the switch ``--pedantic`` is
used, a warning is emitted for every operation that could be re-ordered:

* any operand of a binary adding operation (+,-) that is itself a binary adding
  operation;
* any operand of a binary multiplying operation (\*,/,mod,rem) that is itself a
  binary multiplying operation.

.. _GPS integration:

Running |GNATprove| from GPS
----------------------------

|GNATprove| can be run from GPS. A :menuselection:`SPARK` menu is available
with the following entries:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine All",                "This runs |GNATprove| in flow analysis mode on all files in the project."
   "Examine Root Project",       "This runs |GNATprove| in flow analysis mode on the entire project."
   "Examine File",               "This runs |GNATprove| in flow analysis mode on the current unit."
   "Prove All",                  "This runs |GNATprove| in proof mode on all files in the project."
   "Prove Root Project",         "This runs |GNATprove| in proof mode on the entire project."
   "Prove File",                 "This runs |GNATprove| in proof mode on the current unit."
   "Show Report",                "This displays the report file generated by |GNATprove|."
   "Clean Proofs",               "This removes all files generated by |GNATprove|."
   "Remove Editor Highlighting", "This removes highlighting generated by using |GNATprove|."

The menus :menuselection:`SPARK --> * All` runs |GNATprove| on all files in the
project, both in the root project and in projects that are included in the root
project. The menus :menuselection:`SPARK --> * Root Project` only runs
|GNATprove| on files in the root project. If main files are given for the root
project, only those files that are needed to build the main files will be
analyzed. On a project that has neither main files nor includes other projects,
menus :menuselection:`SPARK --> * All` and :menuselection:`SPARK --> * Root
Project` are equivalent.

.. note::

   The changes made by users in the panels raised by these submenus are
   persistent from one session to the other. Be sure to check that the selected
   checkboxes and additional switches that were previously added are still
   appropriate.

When editing an Ada file, |GNATprove| can also be run from the context menu,
which can be obtained by a right click:

.. csv-table::
   :header: "Submenu", "Action"
   :widths: 1, 4

   "Examine File",       "This runs |GNATprove| in flow analysis mode on the current unit."
   "Examine Subprogram", "This runs |GNATprove| in flow analysis mode on the current subprogram."
   "Prove File",         "This runs |GNATprove| in proof mode on the current unit."
   "Prove Subprogram",   "This runs |GNATprove| in proof mode on the current subprogram."
   "Prove Line",         "This runs |GNATprove| in proof mode on the current line."

.. note::

   If you use the SPARK-HiLite GPL 2013 release, a fourth submenu
   :menuselection:`Prove --> Show Path` is present in the contextual menu, that
   displays a path in the editor corresponding to the current error
   message. This submenu should only be used when displayed after
   right-clicking in the Location View, not after right-clicking in the code
   panel. The path highlighting can be removed by selecting
   :menuselection:`Prove --> Remove Editor Highlighting`.

|GNATprove| project switches can be edited from the panel ``GNATprove`` (in
:menuselection:`Project --> Edit Project Properties --> Switches`).

In some proof modes (``--proof=then_split`` or ``--proof=path_wp``),
|GNATprove| attempts to prove checks separately for the possible paths leading
to a check. If the proof fails on a specific path, the user can display this
path in GPS by clicking on the icon to the left of the failed proof message, or
to the left of the corresponding line in the editor. The path is hidden again
when re-clicking on the same icon.

.. note::

   If you use the SPARK-HiLite GPL 2013 release, the way to display a path
   in GPS is slightly different. Instead of clicking on an icon, you need
   to right-click on the error message in the Location View, and select
   :menuselection:`Prove --> Show Path` in the contextual menu that is raised.

How to View |GNATprove| Output
==============================

In mode ``check``, |GNATprove| prints on the standard output error messages for
|SPARK| violations on all the code for which ``SPARK_Mode`` is ``On``.

In modes ``flow`` and ``prove``, this checking is done as a first phase.

In mode ``flow``, GNATprove prints on the standard output error messages and
warnings for incorrect data flow contracts (annotations ``Global``,
``Depends``, ``Abstract_State``, ``Initializes``, and refinement versions of
these), unitialized variables, and suspicious situations such as
unused assignments, missing return statements and so on.

In mode ``prove`` and report ``fail``, |GNATprove| prints on the standard
output warnings for checks that could not be proved.

In mode ``prove`` and report ``all`` or ``statistics``, |GNATprove| prints on
the standard output warnings for checks that could not be proved, and
information messages for checks proved.

In mode ``all``, GNATprove behaves just as if both modes ``flow`` and
``prove`` were activated.

|GNATprove| always generates :ref:`project statistics` in file
``gnatprove.out``.

.. _project statistics:

Project Statistics
------------------

Based on the automatic detection of which subprograms are in |SPARK|,
|GNATprove| generates global project statistics in file ``gnatprove.out``. The
statistics describe:

* which units were analyzed
* which subprograms in these units were analyzed
* the results of this analysis

Warnings
========

|GNATprove| issues three kinds of warnings, which are controlled separately:

* Compiler warnings are controlled with the usual GNAT compilation switches:

  * ``-gnatws`` suppresses all warnings
  * ``-gnatwa`` enables all optional warnings
  * ``-gnatw?`` enables a specific warning denoted by the last character
    See the GNAT User's Guide for more details. These should passed through
    the compilation switches specified in the project file.

* Flow analysis warnings are controlled with switch ``--warnings``:

  * ``--warnings=off`` suppresses all warnings
  * ``--warnings=on`` issues warnings
  * ``--warnings=error`` treats warnings as errors
    The default is to treat |GNATprove| specific warnings as errors.

* Proof warnings are currently not suppressible

Both compiler and flow analysis warnings can be suppressed selectively by the
use of ``pragma Warnings`` in the source code. See |GNAT Pro| Reference Manual
for more details.

Warning and Error Messages
==========================

This section lists the different error messages and warnings which |GNATprove|
may output. Each message points to a very specific place in the source code.
For example, if a source file ``file.adb`` contains a division as follows::

      if X / Y > Z then ...

|GNATprove| may output a message such as::

   file.adb:12:37: warning: divide by zero might fail

where the division sign ``/`` is precisely on line 12, column 37. Looking at
the explanation in the first table below, which states that a division check
verifies that the divisor is different from zero, it is clear that the message
is about ``Y``, and that |GNATprove| was unable to prove that ``Y`` cannot be
zero. The explanations in the table below should be read with the context that
is given by the source location.

The left column of the table contains the *tag* for each error message. Using
option ``--show-tag``, |GNATprove| prints the tag for each error message at the
end of the message, in brackets.

The following table shows the kinds of warnings issued by proof.

.. csv-table::
   :header: "Message Tag", "Explanation"
   :widths: 1, 4

   "division_check", "Check that the second operand of the division, mod or rem operation is different from zero."
   "index_check", "Check that the given index is within the bounds of the array."
   "overflow_check", "Check that the result of the given arithmetic operation is within the bounds of the base type."
   "range_check", "Check that the given value is within the bounds of the expected scalar subtype."
   "length_check", "Check that the given array is of the length of the expected array subtype."
   "discriminant_check", "Check that the discriminant of the given discriminant record has the expected value. For variant records, this can happen for a simple access to a record field. But there are other cases where a fixed value of the discriminant is required."
   "initial_condition", "Check that the initial condition of a package is true after elaboration."
   "precondition", "Check that the precondition aspect of the given call evaluates to True."
   "postcondition", "Check that the postcondition aspect of the subprogram evaluates to True."
   "contract_case", "Check that all cases of the contract case evaluate to true at the end of the subprogram."
   "disjoint_contract_cases", "Check that the cases of the contract cases aspect are all mutually disjoint."
   "complete_contract_cases", "Check that the cases of the contract cases aspect cover the state space that is allowed by the precondition aspect."
   "loop_invariant_initialization", "Check that the loop invariant evaluates to True on the first iteration of the loop."
   "loop_invariant_preservation", "Check that the loop invariant evaluates to True at each further iteration of the loop."
   "loop_variant", "Check that the given loop variant decreases/increases as specified during each iteration of the loop. This implies termination of the loop."
   "assertion", "Check that the given assertion evaluates to True."

The following table shows all flow analysis messages, which come in three
classes: I(nitialization) errors are the most serious flow errors as not fixing
them might result in a program which can raise a constraint error at run
time. F(low) errors indicate a serious problem with a dependency relation, if
such an error is not fixed, the dependency relations cannot be relied on. All
other unclassified messages are warnings about questionable code constructs.

.. csv-table::
   :header: "Message Tag", "Class", "Explanation"
   :widths: 1, 1, 6

   "depends_missing", "F", "A dependency is missing from the dependency relation."
   "depends_missing_clause", "F", "An out parameter or global is missing from the dependency relation."
   "depends_null", "F", "A variable is missing from the null dependency."
   "depends_wrong", "F", "A stated dependency is not fulfilled."
   "illegal_update", "I", "Flow analysis has detected an update of an in mode global."
   "ineffective",, "Flow analysis has detected an ineffective statement, such as an unused assignment."
   "unused_initial_value",, "An in or in out parameter or global has been found which does not have any effect on any out or in out parameter or global."
   "stable",, "A questionable loop construct where a variable is assigned the same value on each loop iteration."
   "uninitialized", "I", "Flow analysis has detected the use of an uninitialized variable."
   "unused",, "A global or locally declared variable is never used."

.. _how to write loop invariants:

..
   How to Write Loop Invariants
   ============================

   .. todo:: Edit. Add example.

   Proving loops is often the most challenging part of the proof
   activity, both for automatic provers and for users guiding the proof
   tool. It is not uncommon that a proof attempt of a valid loop property
   fails.

   When proving loops, failed proof attempts may need to be "debugged",
   see :ref:`investigate`. In this section we provide a systematic guide
   on proving loops. We will see how failed proof attempts give valuable
   insights, the loop invariant can be mended, and proof attempted again.

   Loop Invariants
   ---------------
   Loop invariants are a powerful way to guide an automatic proof tool to
   successful proof. Though the loop invariant is a rather simple
   concept, the use of it can be quite complicated. Let us start with an
   important observation to make it easier.

   Impact of the Loop Invariant
   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   * Observation: The choice of loop invariant greatly influences the
     proof (attempt) because it is instantiated at 4 occasions in 3
     branches of the proof. 1) Establish loop invariant, 2) Preserve loop
     invariant (two instances), and 3) Use loop invariant (to establish
     postcondition).

   * The trick in successful loop invariant writing is to use this
     observation early in the process and benefit from working out the
     summary of all constraints implied by each branch as early as
     possible.

   Guiding Loop Proofs
   -------------------

   We now go through the most important guiding choices for loop proof,
   the choice of 1) the loop variable and 2) the loop invariant.

   Loop Variable
   ^^^^^^^^^^^^^
   * It is important to identify the loop variable to get the loop invariant right.

   * This is often trivial; for example for for-loops, or when there is
     only one variable.

   * Trick: look at the terminating condition of the loop. The loop
     variable should of course also be updated in the loop.

   * Make a note of how the loop variable is updated in every iteration
     of the loop.

   * The loop variable is also used to write a loop variant for proving
     termination of the loop, but this is not mandatory.

   Loop Invariant
   ^^^^^^^^^^^^^^

   * The loop invariant represents what we really want to prove with the
     induction. This formula depends on the loop variable.

   * To create the loop invariant, start with your proof obligation. What
     property do you need to have proved after the loop? Then edit this
     formula so that your loop variable appears in the right place (clues
     here).

   * Analyse the failed proof attempt if any. Consider for which proof
     obligations the proof fails.  Is it in the establishment,
     preservation, or use of the loop invariant that proof fails?

   * First: If the use case proof obligation fails (corresponding to the loop
     having terminated, i.e. false loop condition), look at this first,
     since this is the hardest constraint.

   * If the preservation of the loop invariant fails to prove, consider
     generalisation of the loop invariant. Many times we can work around
     our loop proof problem by proving a stronger than is actually needed
     and then prove that if the stronger property holds, the original
     proof obligation also holds. This is called generalisation since the
     new, stronger loop invariant is a generalisation of the original
     invariant we were trying to prove.

   * Next: Is it the establishment of the loop invariant that fails?  If
     the rest of the loop proof has succeded, the reason for this failure
     is external to the loop. Consider if the precondition of your loop
     is strong enough? Maybe you need some more initialisation code
     before your loop? Or a pre-condition to the subprogram? Lastly,
     consider if your loop invariant is too strong? Is it contradictory?

   As mentioned earlier, any change to the loop invariant propagates to
   several branches of the proof. In particular a generalisation of the
   loop invariant both introduces more assumptions and - simultaneously
   and in different branches of the tree - increases the proof
   burden. Therefore a patch to the loop invariant based on the
   information from one failed proof branch is likely to cause another
   branch to fail. The suggested order of consideration given above is a heuristic that has shown to work well in practise.

.. _investigate:

How to Investigate Unproved Checks
==================================

One of the most challenging aspects of formal verification is the analysis of
failed proofs. If |GNATprove| fails to prove automatically that a run-time
check or an assertion holds, there might be various reasons:

* [CODE] The check or assertion does not hold, because the code is wrong.
* [ASSERT] The assertion does not hold, because it is incorrect.
* [SPEC] The check or assertion cannot be proved, because of some missing
  assertions about the behavior of the program.
* [TIMEOUT] The check or assertion is not proved because the prover timeouts.
* [PROVER] The check or assertion is not proved because the prover is not smart
  enough.

Investigating Incorrect Code or Assertion
-----------------------------------------

The first step is to check whether the code is incorrect [CODE] or the
assertion is incorrect [ASSERT], or both. Since run-time checks and assertions
can be executed at run time, one way to increase confidence in the correction
of the code and assertions is to test the program on representative inputs. The
following GNAT switches can be used:

* ``-gnato``: enable run-time checking of intermediate overflows
* ``-gnat-p``: reenable run-time checking even if ``-gnatp`` was used to
  suppress all checks
* ``-gnata``: enable run-time checking of assertions

Investigating Unprovable Properties
-----------------------------------

The second step is to consider whether the property is provable [SPEC].  A
check or assertion might be unprovable because a necessary annotation is
missing:

* the precondition of the enclosing subprogram might be too weak; or
* the postcondition of a subprogram called might be too weak; or
* a loop invariant for an enclosing loop might be too weak; or
* a loop invariant for a loop before the check or assertion might be too weak.

In particular, |GNATprove| does not look into subprogram bodies, so all the
necessary information for calls should be explicit in the subprogram
contracts. A focused manual review of the code and assertions can efficiently
diagnose many cases of missing annotations. Even when an assertion is quite
large, |GNATprove| precisely locates the part that it cannot prove, which can
help figuring out the problem. It may useful to simplify the code during this
investigation, for example by adding a simpler assertion and trying to prove
it.

|GNATprove| provides path information that might help the code review. You can
display inside the editor the path on which the proof failed, as described in
:ref:`GPS integration`. In many cases, this is sufficient to spot a missing
assertion. To further assist the user, we plan to add to this path some
information about the values taken by variables from a counterexample.

Investigating Prover Shortcomings
---------------------------------

The last step is to investigate if the prover would find a proof given enough
time [TIMEOUT] or if another prover can find a proof [PROVER]. To that end,
|GNATprove| provides options ``--timeout`` and ``--prover``, usable either from
the command-line (see :ref:`command line`) or inside GPS (see :ref:`GPS
integration`).

Note that for the above experiments, it is quite convenient to use the
:menuselection:`SPARK --> Prove Line` or :menuselection:`SPARK --> Prove
Subprogram` menus in GPS, as described in :ref:`GPS integration`, to get faster
results for the desired line or subprogram.

A common limitation of automatic provers is that they don't handle well
non-linear arithmetic. For example, they might fail to prove simple checks
involving multiplication, division, modulo or exponentiation.

In that case, a user may either:

* manually review the unproved checks and record that they can be trusted (for
  example by storing the result of |GNATprove| under version control), or
* add an assumption in the code to help the prover, in the form of a ``pragma
  Assume``. |GNATprove| assumes it holds, so does not attempt to prove it, and
  uses it in subsequent code. The assumption can be manually reviewed like
  mentioned above, and marking it as an assumption in the code helps
  documenting it.

We plan to provide a `user view` of the formula passed to the prover, for
advanced users to inspect. This view will express in an Ada-like syntax the
actual formula whose proof failed, to make it easier for users to interpret it.
This format is yet to be defined.

For very advanced users, in particular those who would like to do manual proof,
we will provide a description of the format of the proof files generated by
|GNATprove|, so that users can understand the actual files passed to the
prover. Each individual file is stored under the sub-directory ``gnatprove`` of
the project object directory (default is the project directory). The file name
follows the convention::

  <file>_<line>_<column>_<check>_<num>.why

where:

* ``file`` is the name of the Ada source file for the check or assertion
* ``line`` is the line where the check or assertion appears
* ``column`` is the column
* ``check`` is an identifier for the check or assertion
* ``num`` is an optional number and identifies different paths through the
  program, between the start of the subprogram and the location of the check or
  assertion

For example, the proof files for a range check at line 160, column 42, of the
file ``f.adb`` are stored in::

  f.adb_160_42_range_check.why
  f.adb_160_42_range_check_2.why
  f.adb_160_42_range_check_3.why
  ...

The syntax of these files depend on the prover that was used. By default, it is
Alt-Ergo, so these files are in Why3 proof syntax.

To be able to inspect these files, you should instruct |GNATprove| to keep them
around by adding the switch ``-d`` to |GNATprove|'s command line. You can also
use the switch ``-v`` to get a detailed log of which proof files |GNATprove| is
producing and attempting to prove.

|GNATprove| by Example
======================

|GNATprove| is based on advanced technology for modular static analysis and
deductive verification. It is very different both from compilers, which do very
little analysis of the code, and static analyzers, which execute symbolically
the program. |GNATprove| does a very powerful local analysis of the program,
but it does not cross subprogram boundaries. Instead, it uses the subprogram
contracts provided by users to interpret the effect of calls.  Thus, it is
essential to understand how |GNATprove| uses contracts, as well as other forms
of annotations. This section aims at providing a deeper insight into how
|GNATprove| flow analysis and formal verification works, through a
step-by-step exploration of simple code examples.

This section is structured into the following subsections:

.. contents::
  :depth: 1
  :local:

.. _flow_examples:

.. include:: gnatprove_by_example/flow.rst

.. _basic_examples:

.. include:: gnatprove_by_example/basic.rst

.. _call_examples:

.. include:: gnatprove_by_example/call.rst

.. _loop_examples:

.. include:: gnatprove_by_example/loop.rst

.. .. _advanced_examples:

.. .. include:: gnatprove_by_example/advanced.rst
