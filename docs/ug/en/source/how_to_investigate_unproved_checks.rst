.. index:: Silver level; investigate unproved checks
           Gold level; investigate unproved checks

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
  limitations in the model used by |GNATprove|.
* [TIMEOUT] The check or assertion is not proved because the prover
  timeouts.
* [PROVER] The check or assertion is not proved because the prover is not
  smart enough.

.. index:: executable contracts; investigate unproved checks

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

The second step is to consider whether the property is provable [SPEC]. A
check or assertion might be unprovable because a necessary annotation is
missing:

* the precondition of the enclosing subprogram might be too weak; or
* the postcondition of a subprogram called might be too weak; or
* a loop invariant for an enclosing loop might be too weak; or
* a loop invariant for a loop before the check or assertion might be too weak.

.. index:: tool interaction; possible fix

In particular, |GNATprove| does not look into subprogram bodies, so all the
necessary information for calls should be explicit in the subprogram
contracts. |GNATprove| may emit a tentative fix for the unprovable
property when it suspects a missing precondition, postcondition or loop
invariant to be the cause of the unprovability. The fix part follows
the usual message of the form::

   file:line:col: severity: check might fail

with a text such as::

   possible fix: subprogram at line xxx should mention Var in a precondition
   possible fix: loop at line xxx should mention Var in a loop invariant
   possible fix: call at line xxx should mention Var in a postcondition

A focused manual review of the code and assertions can
efficiently diagnose many cases of missing annotations. Even when an
assertion is quite large, |GNATprove| precisely locates the part that it
cannot prove, which can help figuring out the problem. It may useful to
simplify the code during this investigation, for example by adding a
simpler assertion and trying to prove it.

.. index:: counterexample; investigate unproved checks

|GNATprove| provides path information that might help the code review. You can
display inside the editor the path on which the proof failed, as described in
:ref:`Running GNATprove from GNAT Studio`. In some cases, a counterexample is also
generated on the path, with values of variables which exhibit the problem (see
:ref:`Understanding Counterexamples`). In many cases, this is sufficient to
spot a missing assertion.

A property can also be conceptually provable, but the model used by
|GNATprove| can currently not reason about it [MODEL]. (See
:ref:`GNATprove Limitations` for a list of the current limitations in
|GNATprove|.) In particular using the following features of the language
may yield checks that should be true, but cannot be proved:

* Floating point arithmetic (although using |CodePeer| integration may help
  here)
* The specific value of dispatching calls when the tag is known

To use |CodePeer| integration, pass the switch ``--codepeer=on`` to
|GNATprove|. In those cases where no prover, including |CodePeer|, can prove
the check, the missing information can usually be added using ``pragma Assume``.

.. index:: ghost code; investigate unproved checks

It may be difficult sometimes to distinguish between unprovable properties and
prover shortcomings (the next section). The most generally useful action to
narrow down the issue to its core is to insert assertions in the code that
`test` whether the property (or part of it) can be proved at some specific
point in the program. For example, if a postcondition states a property (P or
Q), and the implementation contains many branches and paths, try adding
assertions that P holds or Q holds where they are expected to hold. This can
help distinguish between the two cases:

* In the case of an unprovable property, this may point to a specific path in
  the program, and a specific part of the property, which cause the issue.
* In the case of a prover shortcoming, this may also help provers to manage to
  prove both the assertion and the property. Then, it is good practice to keep
  in the code only those assertions that help getting automatic proof, and to
  remove other assertions that were inserted during interaction.

.. index:: --info; investigate unproved checks

When using switch ``--info``, |GNATprove| issues information messages regarding
internal decisions that could influence provability:

* whether candidate loops for :ref:`Automatic Unrolling of Simple For-Loops`
  are effectively unrolled or not;
* whether candidate subprograms for :ref:`Contextual Analysis of Subprograms
  Without Contracts` are effectively inlined for proof or not;
* whether possible subprogram nontermination impacts the proof of calls to that
  subprogram (see the note in the section on :ref:`Subprogram Termination`)

.. index:: --level; investigate unproved checks

Investigating Prover Shortcomings
---------------------------------

The last step is to investigate if the prover would find a proof given enough
time [TIMEOUT] or if another prover can find a proof [PROVER]. To that end,
|GNATprove| provides switch ``--level``, usable either from the command-line
(see :ref:`Running GNATprove from the Command Line`), inside GNAT Studio (see
:ref:`Running GNATprove from GNAT Studio`) or inside GNATbench (see :ref:`Running
GNATprove from GNATbench`). The level of 0 is only adequate for simple
proofs. In general, one should increase the level of proof (up to level 4)
until no more automatic proofs can be obtained.

As described in the section about :ref:`Running GNATprove from the Command
Line`, switch ``--level`` is equivalent to setting directly various lower
level switches like ``--timeout``, ``--prover``, and ``--proof``. Hence, one
can also set more powerful (and thus leading to longer proof time) values
for the individual switches rather than using the predefined combinations
set through ``--level``.

.. index:: tool interaction; prove line or subprogram

Note that for the above experiments, it is quite convenient to use the
:menuselection:`SPARK --> Prove Line` or :menuselection:`SPARK --> Prove
Subprogram` menus in GNAT Studio, as described in :ref:`Running GNATprove from GNAT Studio` and
:ref:`Running GNATprove from GNATbench`, to get faster results for the desired
line or subprogram.

A current limitation of automatic provers is that they don't handle
floating-point arithmetic very precisely, in particular when there are either a
lot of operations, or some non-linear operations (multiplication, division,
exponentiation). In that case, it may be profitable to use |CodePeer|
integration, which is activated with the switch ``--codepeer=on``, as |CodePeer|
is both fast and precise for proving bounds of floating-point operations.

Another common limitation of automatic provers is that they don't handle
non-linear arithmetic well. For example, they might fail to prove simple checks
involving multiplication, division, modulo or exponentiation.

In that case, a user may either:

* add in the code a call to a lemma from the SPARK lemma library (see details
  in :ref:`Manual Proof Using SPARK Lemma Library`), or
* add in the code a call to a user lemma (see details in :ref:`Manual Proof
  Using User Lemmas`), or
* add an assumption in the code (see details in :ref:`Indirect Justification
  with Pragma Assume`), or
* add a justification in the code (see details in :ref:`Direct Justification
  with Pragma Annotate`), or
* get a `user view` of the formula passed to the prover, and complete the proof
  interactively (see details in :ref:`Manual Proof Within GNAT Studio`), or
* manually review the unproved checks and record that they can be trusted
  (for example by storing the result of |GNATprove| under version control).

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

.. index:: .spark files

Looking at Machine-Parsable |GNATprove| Output
----------------------------------------------

|GNATprove| generates files which contain the results of SPARK analysis in
machine-parsable form. These files are located in the ``gnatprove``
subdirectory of the project object directory, and have the suffix ``.spark``.
The structure of these files exposes internal details such as the exact way
some checks are proved, therefore the structure of these files may change. Still,
we provide here the structure of these files for convenience.

At various places in these files, we refer to entities. These are Ada
entities, either subprograms or packages. Entities are defined by their name and
their source location (file and line). In JSON this translates to the
following dictionary for entities::

  { "name" : string,
    "file" : string,
    "line" : int }

A ``.spark`` file is of this form::

  { "spark" : list spark_result,
    "flow"  : list flow_result,
    "proof" : list proof_result }

Each entry is mapped to a list of entries whose format is described below.

The ``spark_result`` entry is simply an entity, with an extra field for spark
status, so that the entire dictionary looks like this::

  spark_result = { "name"  : string,
                   "file"  : string,
                   "line"  : int,
                   "spark" : string }

Field "spark" takes value in "spec", "all" or "no" to denote
respectively that only the spec is in SPARK, both spec/body are in SPARK
(or spec is in SPARK for a package without body), or the spec is not in
SPARK.

Entries for proof are of the following form::

  proof_result =
    { "file"       : string,
      "line"       : int,
      "col"        : int,
      "suppressed" : string,
      "rule"       : string,
      "severity"   : string,
      "tracefile"  : string,
      "check_tree" : list goal,
      "msg_id"     : int,
      "how_proved" : string,
      "entity"     : entity }

* ("file", "line", "col") describe the source location of the message.
* "rule" describes the kind of check.
* "severity" describes the kind status of the message, possible values used
  by gnatwhy3 are "info", "low", "medium", "high" and "error".
* "tracefile" contains the name of a trace file, if any.
* "entity" contains the entity dictionary for the entity that this check
  belongs to.
* "msg_id" - if present indicates that this entry corresponds to a message
  issued on the commandline, with the exact same msg_id in brackets:
  "[#12]"
* "suppressed" - if present, the message is in fact suppressed by a pragma
  Annotate, and this field contains the justification message.
* "how_proved" - if present, indicates how the check has been proved (i.e.
  which prover). Special values are "interval" and "codepeer", which
  designate the special interval analysis, done in the frontend, and the
  CodePeer analysis, respectively. Both have their own column in the
  summary table.
* "check_tree" basically contains a copy of the session
  tree in JSON format. It's a tree structure whose nodes are goals,
  transformations and proof attempts::

   goal = { "transformations" : list trans,
            "pa"              : proof_attempt }

   trans = { [transname : goal] }

   proof_attempt = { [prover : infos] }

   infos = { "time"   : float,
             "steps"  : integer,
             "result" : string }


Flow entries are of the same form as for proof. Differences are in the
possible values for "rule", which can only be the ones for flow messages.
Also "how_proved" field is never set.

.. index:: --proof; proof strategies

Understanding Proof Strategies
------------------------------

We now explain in more detail how the provers are run on the logical formula(s)
generated for a given check, a.k.a. Verification Conditions or VCs.

* In ``per_check`` mode, a single VC is generated for each check at the source
  level (e.g. an assertion, run-time check, or postcondition); in some cases two
  VCs can appear. Before attempting proof, this VC is then split into the
  conjuncts, that is, the parts that are combined with ``and`` or ``and
  then``. All provers are tried on the VCs obtained in this way until one of
  them proves the VC or no more provers are left.
* In ``per_path`` mode, a VC is generated not only for each check at the source
  level, but for each path to the check. For example, for an assertion that
  appears after an if-statement, at least two VCs will be generated - one
  for each path through the if-statement. For each such VC, all provers are
  attempted. Unproved VCs are then further split into their conjuncts,
  and proof is again attempted.
* In ``progressive`` mode, first the actions described for ``per_check`` are
  tried. For all unproved VCs, the VC is then split into the paths that lead
  to the check, like for ``per_path``. Each part is then
  attempted to be proved independently.
