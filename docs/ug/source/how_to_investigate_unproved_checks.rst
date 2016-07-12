.. _How to Investigate Unproved Checks:

How to Investigate Unproved Checks
==================================

One of the most challenging aspects of formal verification is the analysis
of failed proofs. If |GNATprove| fails to prove automatically that a
run-time check or an assertion holds, there might be various reasons:

* [CODE] The check or assertion does not hold, because the code is wrong.
* [ASSERT] The assertion does not hold, because it is incorrect.
* [SPEC] The check or assertion cannot be proved, because of some missing
  assertions about the behavior of the program.
* [MODEL] The check or assertion is not proved because of current
  limitations in the model used by |GNATProve|.
* [TIMEOUT] The check or assertion is not proved because the prover
  timeouts.
* [PROVER] The check or assertion is not proved because the prover is not
  smart enough.

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

.. _Investigating Unprovable Properties:

Investigating Unprovable Properties
-----------------------------------

The second step is to consider whether the property is provable [SPEC]. A
check or assertion might be unprovable because a necessary annotation is
missing:

* the precondition of the enclosing subprogram might be too weak; or
* the postcondition of a subprogram called might be too weak; or
* a loop invariant for an enclosing loop might be too weak; or
* a loop invariant for a loop before the check or assertion might be too weak.

In particular, |GNATprove| does not look into subprogram bodies, so all the
necessary information for calls should be explicit in the subprogram
contracts. A focused manual review of the code and assertions can
efficiently diagnose many cases of missing annotations. Even when an
assertion is quite large, |GNATprove| precisely locates the part that it
cannot prove, which can help figuring out the problem. It may useful to
simplify the code during this investigation, for example by adding a
simpler assertion and trying to prove it.

|GNATprove| provides path information that might help the code review. You can
display inside the editor the path on which the proof failed, as described in
:ref:`Running GNATprove from GPS`. In some cases, a counterexample is also
generated on the path, with values of variables which exhibit the problem (see
:ref:`Understanding Counterexamples`). In many cases, this is sufficient to
spot a missing assertion.

A property can also be conceptually provable, but the model used by
|GNATProve| can currently not reason about it [MODEL]. (See
:ref:`GNATProve_Limitations` for a list of the current limitations in
|GNATProve|.) In particular using the following features of the language
may yield VCs that should be true, but cannot be proved:

* Floating point arithmetic
* The content of string literals

In these cases the missing information can usually be added using ``pragma
Assume``.

.. _Investigating Prover Shortcomings:

Investigating Prover Shortcomings
---------------------------------

The last step is to investigate if the prover would find a proof given enough
time [TIMEOUT] or if another prover can find a proof [PROVER]. To that end,
|GNATprove| provides switch ``--level``, usable either from the command-line
(see :ref:`Running GNATprove from the Command Line`), inside GPS (see
:ref:`Running GNATprove from GPS`) or inside GNATbench (see :ref:`Running
GNATprove from GNATbench`). The default level of 0 is only adequate for simple
proofs. In general, one should increase the level of proof (up to level 4)
until no more automatic proofs can be obtained.

As described in the section about :ref:`Running GNATprove from the Command
Line`, switch ``--level`` is equivalent to setting directly various lower
level switches like ``--steps``, ``--prover``, and ``--proof``. Hence, one
can also set more powerful (and thus leading to longer proof time) values
for the individual switches rather than using the predefined combinations
set through ``--level``.

Note that for the above experiments, it is quite convenient to use the
:menuselection:`SPARK --> Prove Line` or :menuselection:`SPARK --> Prove
Subprogram` menus in GPS, as described in :ref:`Running GNATprove from GPS` and
:ref:`Running GNATprove from GNATbench`, to get faster results for the desired
line or subprogram.

A common limitation of automatic provers is that they don't handle
non-linear arithmetic well. For example, they might fail to prove simple checks
involving multiplication, division, modulo or exponentiation.

In that case, a user may either:

* add in the code a call to a lemma from the SPARK lemma library (see details
  in :ref:`Manual Proof Using SPARK Lemma Library`), or
* manually review the unproved checks and record that they can be trusted
  (for example by storing the result of |GNATprove| under version control),
  or
* add an assumption in the code to help the prover, in the form of a
  ``pragma Assume``. |GNATprove| assumes it holds, so does not attempt to
  prove it, and uses it in subsequent code. The assumption can be manually
  reviewed like mentioned above, and marking it as an assumption in the
  code helps documenting it, or
* define and call a lemma which makes the missing property available.

The last is a technique which is a combination of expression functions and
``pragma Assume``. For example the below code is currently not provable
with Alt-Ergo using the default setup:

   .. literalinclude:: ../lemmas/example1.adb
      :language: ada
      :linenos:

This code can be made provable by using a lemma. All VCs for this function
are easily proved, showing that the lemma holds in all cases.

   .. literalinclude:: ../lemmas/lemmas.ads
      :language: ada
      :linenos:

Note the postcondition on the expression function ensures that VCs are
generated showing it is always valid. The lemma can then be used though an
assumption (although it is planned to extend ``pragma Assert`` to support
this pattern):

   .. literalinclude:: ../lemmas/example2.adb
      :language: ada
      :linenos:

In the future, |GNATprove| may provide a `user view` of the formula passed to
the prover, for advanced users to inspect. This view would express in an
Ada-like syntax the actual formula whose proof failed, to make it easier for
users to interpret it. This format is yet to be defined.

For advanced users, in particular those who would like to do manual
proof, we will provide a description of the format of the proof files
generated by |GNATprove|, so that users can understand the actual files
passed to the prover. Each individual file is stored under the
sub-directory ``gnatprove`` of the project object directory (default is the
project directory). The file name follows the convention::

  <file>_<line>_<column>_<check>_<num>.<ext>

where:

* ``file`` is the name of the Ada source file for the check
* ``line`` is the line where the check appears
* ``column`` is the column
* ``check`` is an identifier for the check
* ``num`` is an optional number and identifies different paths through the
  program, between the start of the subprogram and the location of the check
* ``ext`` is the extension corresponding to the file format chosen. The format
  of the file depends on the prover used. For example, files for Alt-Ergo are
  are in Why3 format, and files for CVC4 are in SMTLIB2 format.

For example, the proof files generated for prover Alt-Ergo for a range check at
line 160, column 42, of the file ``f.adb`` are stored in::

  f.adb_160_42_range_check.why
  f.adb_160_42_range_check_2.why
  f.adb_160_42_range_check_3.why
  ...

Corresponding proof files generated for prover CVC4 are stored in::

  f.adb_160_42_range_check.smt2
  f.adb_160_42_range_check_2.smt2
  f.adb_160_42_range_check_3.smt2
  ...

To be able to inspect these files, you should instruct |GNATprove| to keep them
around by adding the switch ``-d`` to |GNATprove|'s command line. You can also
use the switch ``-v`` to get a detailed log of which proof files |GNATprove| is
producing and attempting to prove.
