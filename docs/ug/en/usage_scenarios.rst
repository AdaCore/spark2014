**************************
Applying SPARK in Practice
**************************

|SPARK| tools offer different levels of analysis, which are relevant in
different contexts. This section starts with a description of the five
:ref:`Levels of Software Assurance` that can be achieved with SPARK. It
continues with a description of the main :ref:`Objectives of Using SPARK`. This
list gathers the most commonly found reasons for adopting |SPARK| in industrial
projects, but it is not intended to be an exhaustive list.

Whatever the objective(s) of using |SPARK|, any project fits in one of four
possible :ref:`Project Scenarios`:

* the `brown field` scenario: :ref:`Maintenance and Evolution of Existing Ada Software`
* the `green field` scenario: :ref:`New Developments in SPARK`
* the `migration` scenario: :ref:`Conversion of Existing SPARK Software to SPARK 2014`
* the `frozen` scenario: :ref:`Analysis of Frozen Ada Software`

The section :ref:`Project Scenarios` examines each of these scenarios in turn
and describes how |SPARK| can be applied in each case.

The section :ref:`Best Practices` lists common cases that can be difficult to
handle in |SPARK|, and explains the different possibilities.

Levels of Software Assurance
============================

.. The text of this section is largely borrowed from the Guidance document for
   the adoption of SPARK. Changes there should be reflected here when possible.

SPARK analysis can give strong guarantees that a program:

* does not read uninitialized data,
* accesses global data only as intended,
* does not contain concurrency errors (deadlocks and data races),
* does not contain run-time errors (e.g., division by zero or buffer overflow),
  except for ``Storage_Error``, which is not covered by SPARK analysis (see
  also section :ref:`Dealing with Storage_Error` below)
* respects key integrity properties (e.g., interaction between components or global invariants),
* is a correct implementation of software requirements expressed as contracts.

SPARK can analyze either a complete program or :ref:`those parts that are marked
as being subject to analysis<Identifying SPARK Code>`, but it can only be
applied to code that follows :ref:`some restrictions designed to facilitate
formal verification<Language Restrictions>`. In particular, tasking is
restricted to the Ravenscar or Jorvik profiles and use of pointers should
follow a strict ownership
policy aiming at preventing aliasing of allocated data. Pointers and tasking
are both features that, if supported completely, make formal verification, as
done by SPARK, infeasible, either because of limitations of state-of-the-art
technology or because of the disproportionate effort required from users to
apply formal verification in such situations. The large subset of Ada that is
analyzed by SPARK is also called the SPARK language subset.

SPARK builds on the strengths of Ada to provide even more guarantees
statically rather than dynamically. As summarized in the following table,
Ada provides strict syntax and strong typing at compile time plus dynamic
checking of run-time errors and program contracts. SPARK allows
such checking to be performed statically. In addition, it enforces the use of a safer
language subset and detects data flow errors statically.

.. csv-table::
   :header: "", "Ada", "SPARK"
   :widths: 1, 1, 1

   "Contract programming", "dynamic", "dynamic / static"
   "Run-time errors",      "dynamic", "dynamic / static"
   "Data flow errors",     "--",      "static"
   "Strong typing",        "static",  "static"
   "Safer language subset","--",      "static"
   "Strict clear syntax",  "static",  "static"

The main benefit of formal program verification as performed by SPARK is that
it allows verifying properties that are difficult or very costly to verify by
other methods, such as testing or reviews. That difficulty may stem from the
complexity of the software, the complexity of the requirements, and/or the
unknown capabilities of attackers. Formal verification allows giving guarantees
that some properties are always verified, however complex the context. The
latest versions of international certification standards for avionics (DO-178C
/ ED-12C) and railway systems (CENELEC EN 50128:2011) have recognized these
benefits by increasing the role that formal methods can play in the development
and verification of critical software.

Levels of SPARK Use
-------------------

The scope and level of SPARK analysis depend on the objectives being
pursued by the adoption of SPARK. The scope of analysis may be the totality
of a project, only some units, or only parts of units. The level of
analysis may range from simple guarantees provided by flow analysis to
complex properties being proved.  These can be divided into five easily
remembered levels:

#. `Stone level` - valid SPARK
#. `Bronze level` - initialization and correct data flow
#. `Silver level` - absence of run-time errors (AoRTE)
#. `Gold level` - proof of key integrity properties
#. `Platinum level` - full functional proof of requirements

Platinum level is defined here for completeness, but it is seldom applicable
due to the high cost of achieving it. Each level builds on the previous one, so
that the code subject to the Gold level should be a subset of the code subject
to Silver level, which itself is a subset of the code subject to Bronze level,
which is in general the same as the code subject to Stone level. We advise
using:

* Stone level only as an intermediate level during adoption,
* Bronze level for as large a part of the code as possible,
* Silver level as the default target for critical software (subject to costs
  and limitations),
* Gold level only for a subset of the code subject to specific key integrity
  (safety/security) properties,
* Platinum level only for those parts of the code with the highest integrity
  (safety/security) constraints.

Our starting point is a program in Ada, which could be thought of as the
Brick level: thanks to the use of Ada programming language, this level
already provides some confidence: it is the highest level in The Three
Little Pigs fable! And indeed languages with weaker semantics could be
thought of as Straw and Sticks levels. However, the adoption of SPARK
allows us to get stronger guarantees, should the wolf in the fable adopt
more aggressive means of attack than simply blowing.

A pitfall when using tools for automating human tasks is to end up "pleasing
the tools" rather than working around the tool limitations. Both flow analysis
and proof, the two technologies used in SPARK, have known limitations. Users
should refrain from changing the program for the benefit of only getting fewer
messages from the tools. When relevant, users should justify tool messages
through appropriate pragmas. See the sections on :ref:`Suppressing Warnings`
and :ref:`Justifying Check Messages` for more details.

GNATprove can be run at the different levels mentioned in this document, either
through the Integrated Development Environments (IDE) :ref:`GNAT Studio<Running
GNATprove from GNAT Studio>`, :ref:`Visual Studio Code<Running GNATprove from
Visual Studio Code>` or :ref:`Eclipse<Running GNATprove from GNATbench>`, or
:ref:`on the command line<Running GNATprove from the Command Line>`. Use of the
command-line interface at a given level is facilitated by convenient synonyms:

* use switch ``--mode=stone`` for Stone level (synonym of ``--mode=check_all``)
* use switch ``--mode=bronze`` for Bronze level (synonym of ``--mode=flow``)
* use switch ``--mode=silver`` for Silver level (synonym of ``--mode=all``)
* use switch ``--mode=gold`` for Gold level (synonym of ``--mode=all``)

Note that levels Silver and Gold are activated with the same switches. Indeed,
the difference between these levels is not on how GNATprove is run, but on the
objectives of verification. This is explained in the section on :ref:`Gold
Level <Gold Level>`. Platinum level is not given a separate switch value, as it
would be the same.

Sections :ref:`Stone Level <Stone Level>` to :ref:`Platinum Level <Platinum
Level>` present the details of the five levels of software assurance. Each
section consists in a short description of three key aspects of adopting SPARK
at that level:

* `Benefits` - What is gained from adopting SPARK?
* `Impact on Process` - How should the process (i.e., the software life cycle
  development and verification activities) be adapted to use SPARK?
* `Costs and Limitations` - What are the main costs and limitations for
  adopting SPARK?

Additionally, the index of this document contains entries for all levels (from
`Stone level` to `Platinum level`) which point to parts of the User's Guide
relevant for reaching a specific level.

.. index:: Stone level

.. _Stone Level:

Stone Level - Valid SPARK
-------------------------

.. include:: source/stone_level.rst

.. index:: Bronze level

.. _Bronze Level:

Bronze Level - Initialization and Correct Data Flow
---------------------------------------------------

.. include:: source/bronze_level.rst

.. index:: Silver level

.. _Silver Level:

Silver Level - Absence of Run-time Errors (AoRTE)
-------------------------------------------------

.. include:: source/silver_level.rst

.. index:: Gold level

.. _Gold Level:

Gold Level - Proof of Key Integrity Properties
----------------------------------------------

.. include:: source/gold_level.rst

.. index:: Platinum level

.. _Platinum Level:

Platinum Level - Full Functional Correctness
--------------------------------------------

Platinum level is achieved when contracts fully cover the functional
requirements. Achieving the Platinum level is rare in itself, and usually done
for small parts of an application.

.. rubric:: Benefits

The SPARK code is guaranteed to correctly implement its specification,
including being free from all the defects already detected at the Bronze,
Silver and Gold levels. These strong guarantees can be used as arguments in a
safety/security case for the overall software system, providing steps are taken
for :ref:`Managing Assumptions`.

.. rubric:: Impact on Process

The impact on process is mostly the same as for Gold level. When manual proof
is used, which is very likely at this level, there is an associated activity to
maintain these proofs as the code evolves. Typically a dedicated verification
engineer with enough experience of formal program verification in SPARK should
be tasked with this activity.

.. rubric:: Costs and Limitations

These are the same as for Gold level, plus the cost of applying manual proof
more systematically. Depending on the manual proof technique used and the
complexity of the proof, this might be more or less costly initially and during
maintenance:

* :ref:`Manual Proof Using SPARK Lemma Library` is the least costly of all,
  only requiring to use the right lemma from the library.

* :ref:`Manual Proof Using Ghost Code` is more costly, as it requires expertise
  and interactions with the tool to guide automatic provers.

* :ref:`Manual Proof Using Coq` is the most costly, as it require expertise in
  interactive proof as well as knowledge of the syntax of the Coq interactive
  prover.

While the use of manual proof allows to prove any provable property in
principle, a balance needs to be found between the higher cost of manual proof
techniques and the benefits they bring compared to testing or manual
justification.

Objectives of Using SPARK
=========================

.. index:: Stone level; safe coding standard

Safe Coding Standard for Critical Software
------------------------------------------

|SPARK| is a subset of Ada meant for formal verification, by excluding features
that are difficult or impossible to analyze automatically. This means that
|SPARK| can also be used as a coding standard to restrict the set of features
used in critical software. As a safe coding standard checker, |SPARK| allows
both to prevent the introduction of errors by excluding unsafe Ada features,
and it facilitates their early detection with |GNATprove|'s flow analysis.

Exclusion of Unsafe Ada Features
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Once the simple task of :ref:`Identifying SPARK Code` has been completed, one
can use |GNATprove| in ``check`` mode to verify that |SPARK| restrictions are
respected in |SPARK| code. Here we list some of the most error-prone Ada
features that are excluded from |SPARK| (see :ref:`Excluded Ada Features` for
the complete list).

* All expressions, including function calls, are free of
  side-effects. Expressions with side-effects are problematic because they hide
  interactions that occur in the code, in the sense that a computation will not
  only produce a value but also modify some hidden state in the program. In the
  worst case, they may even introduce interferences between subexpressions of a
  common expression, which results in different executions depending on the
  order of evaluation of subexpressions chosen by the compiler.

* The use of access types and allocators is restricted to pool specific
  access types and subject to an ownership policy ensuring that a mutable
  memory cell has a single owner. In general, pointers can
  introduce aliasing, that is, they can allow the same object to be visible
  through different names at the same program point. This makes it difficult to
  reason about a program as modifying the object under one of the names will
  also modify the other names.  What is more, access types come with their own
  load of common mistakes, like double frees and dangling pointers.

* |SPARK| also prevents dependencies on the elaboration order by ensuring that
  no package can write into variables declared in other packages during its
  elaboration. The use of controlled types is also forbidden as they lead to
  insertions of implicit calls by the compiler. Finally, backward goto
  statements are not permitted as they obfuscate the control flow.

.. index:: Bronze level; early detection of errors

Early Detection of Errors
^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove|'s flow analysis will find all the occurrences of the following
errors:

* uses of uninitialized variables (see :ref:`Data Initialization Policy`)

* aliasing of parameters that can cause interferences, which are often not
  accounted for by programmers (see :ref:`Absence of Interferences`)

It will also warn systematically about the following suspicious behaviors:

* wrong parameter modes (can hurt readability and maintainability or even be
  the sign of a bug, for example if the programmer forgot to update a
  parameter, to read the value of an out parameter, or to use the initial value
  of a parameter)

* unused variables or statements (again, can hurt readability and
  maintainability or even be the sign of a bug)

.. index:: Silver level; absence of run-time errors

Prove Absence of Run-Time Errors (AoRTE)
----------------------------------------

With Proof Only
^^^^^^^^^^^^^^^

|GNATprove| can be used to prove the complete absence of possible run-time
errors corresponding to:

* all possible explicit raising of unexpected exceptions in the program,

* raising exception ``Constraint_Error`` at run time, and

* all possible failures of assertions corresponding to raising exception
  ``Assert_Error`` at run time.

AoRTE is important for ensuring safety in all possible operational conditions
for safety-critical software (including boundary conditions, or abnormal
conditions) or for ensuring availability of a service (absence of DOS attack
that can crash the software).

When run-time checks are enabled during execution, Ada programs are not
vulnerable to the kind of attacks like buffer overflows that plague programs in
C and C++, which allow attackers to gain control over the system. But in the
case where run-time checks are disabled (in general for efficiency, but it
could be for other reasons), proving their absence with |GNATprove| also
prevents such attacks. This is specially important for ensuring security when
some inputs may have been crafted by an attacker.

Few subprogram contracts (:ref:`Preconditions` and :ref:`Postconditions`) are
needed in general to prove AoRTE, far fewer than for proving functional
properties. Even fewer subprogram contracts are needed if types are suitably
constrained with :ref:`Type Contracts`. Typically, 95% to 98% of run-time
checks can be proved automatically, and the remaining checks can be either
verified with manual provers or justified by manual analysis.

|GNATprove| supports this type of combination of results in the summary table
of :ref:`The Analysis Results Summary File`. Multiple columns display the
number of checks automatically verified, while the column `Justified` displays
the number of checks manually justified. The column `Unproved` should be empty
for all checks to be verified.

.. index:: executable contracts; combining proof and test

With a Combination of Proof and Test
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

It is not always possible to achieve 100% proof of AoRTE, for multiple reasons:

#. Formal verification is only applicable to the part of the program that is in
   |SPARK|. If the program includes parts in Ada that are not in |SPARK|, for
   example, then it is not possible to prove AoRTE on those parts.

#. Some run-time checks may not be proved automatically due to prover
   shortcomings (see :ref:`Investigating Prover Shortcomings` for details).

#. ``Storage_Error`` exceptions are not covered by SPARK analysis.

#. It may not be cost-effective to add the required contracts for proving AoRTE
   in a less critical part of the code, compared to using testing as a means of
   verification.

For all these reasons, it is important to be able to combine the results of
formal verification and testing on different parts of a codebase. Formal
verification works by making some assumptions, and these assumptions should be
shown to hold even when formal verification and testing are
combined. Certainly, formal verification cannot guarantee the same properties
when part of a program is only tested, as when all of a program is proved. The
goal then, when combining formal verification and testing, is to reach a level
of confidence as good as the level reached by testing alone.

At the Level of Individual Run-Time Checks
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One way to get confidence that unproved run-time checks cannot fail during
execution is to exercise them during testing. Test coverage information allows
guaranteeing a set of run-time checks have been executed successfully during a
test run. This coverage information may be gathered from the execution of a
unit testing campaign, an integration testing campaign, or the execution of a
dedicated testsuite focussing on exercising the run-time checks (for example on
boundary values or random ones).

This strategy is already applied in other static analysis tools, for example
in the integration between the |CodePeer| static analyzer and the VectorCAST
testing tool for Ada programs.

Between Proof and Integration Testing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracts can also be exercised dynamically during integration testing. In
cases where unit testing is not required (either because proof has been applied
to all subprograms, or because the verification context allows it), exercising
contracts during integration testing can complement proof results, by giving
the assurance that the actual compiled program behaves as expected.

This strategy has been applied at Capgemini Engineering on UK military projects
submitted to Def Stan 00-56 certification: AoRTE was proved on all the code,
and contracts were exercised during integration testing, which allowed to scrap
unit testing.

Between Proof and Unit Testing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contracts on subprograms provide a natural boundary for combining proof and
test:

* If proof is used to demonstrate that a subprogram is free of run-time errors
  and respects its contract, this proof depends on these properties being respected at the call site:

  * the precondition of the subprogram;
  * all inputs (including global variables) of the subprogram contain valid
    data for their types;
  * the Anti-Aliasing rules in SPARK RM 6.4.2 are respected.

  This verification can be achieved by proving the caller too, or, in the case
  of the precondition, by checking it dynamically during unit testing of the
  caller.

* If proof is used to demonstrate that a subprogram is free of run-time errors
  and respects its contract, and this subprogram calls other subprograms, this
  proof depends on the postconditions of the called subprogram being respected
  at call sites. This verification can be achieved by proving the callees too,
  or by checking dynamically the postcondition of the called subprograms during
  their unit testing.

Thus, it is possible to combine freely subprograms that are proved and
subprograms that are unit tested, provided subprogram contracts
(:ref:`Preconditions` and :ref:`Postconditions`) are exercised during unit
testing. This can be achieved by compiling the program with assertions for
testing (for example with switch ``-gnata`` in |GNAT Pro|), or by using
GNATtest to create the test harness (see section 7.10.12 of |GNAT Pro| User's
Guide on `Testing with Contracts`).

When combining proof and test on individual subprograms, one should make sure
that the assumptions made for proof are justified at the boundary between
proved subprograms and tested subprograms (see section on :ref:`Managing
Assumptions`). To help with this verification, special switches are defined in
|GNAT Pro| to add run-time checks that verify dynamically the assumptions made
during proof:

* ``-gnateA`` adds checks that parameters are not aliased
* ``-gnateV`` adds checks that parameters are valid, including parameters of
  composite types (arrays, records)
* ``-gnatVa`` adds checks that objects are valid at more places than -gnateV,
  but only for scalar objects

This strategy is particularly well suited in the context of the DO-178C
certification standard in avionics, which explicitly allows proof or test to be
used as verification means on each module.

.. index:: Gold level; correct component integration

Prove Correct Integration Between Components
--------------------------------------------

Correct Integration In New Developments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| can be used to prove correct integration between components, where
a component could be a subprogram, a unit or a set of units. Indeed, even if
components are verified individually (for example by proof or test or a
combination thereof), their combination may still fail because of unforeseen
interactions or design problems.

|SPARK| is ideally equipped to support such analysis, with its detailed
:ref:`Subprogram Contracts`:

* With :ref:`Data Dependencies`, a user can specify exactly the input and
  output data of a subprogram, which goes a long way towards uncovering
  unforeseen interactions.

* With functional contracts (:ref:`Preconditions` and :ref:`Postconditions`), a
  user can specify precisely properties about the behavior of the subprogram
  that are relevant for component integration. In general, simple contracts are
  needed for component integration, which means that they are easy to write and
  to verify automatically. See section on :ref:`Writing Contracts for Program
  Integrity` for examples of such contracts.

When using data dependencies, |GNATprove|'s flow analysis is sufficient to
check correct integration between components. When using functional contracts,
|GNATprove|'s proof should also be applied.

In Replacement of Comments
^^^^^^^^^^^^^^^^^^^^^^^^^^

It is good practice to specify properties of a subprogram that are important
for integration in the comments that are attached to the subprogram
declaration.

Comments can be advantageously replaced by contracts:

* Comments about the domain of the subprogram can be replaced by
  :ref:`Preconditions`.

* Comments about the effects of the subprogram can be replaced by
  :ref:`Postconditions` and :ref:`Data Dependencies`.

* Comments about the result of functions can be replaced by
  :ref:`Postconditions`.

* |GNATprove| can use the contracts to prove correct integration between
  components, as in new developments.

Contracts are less ambiguous than comments, and can be accompanied by (or
interspersed with) higher level comments that need not be focused on the finer
grain details of which variables must have which values, as these are already
specified concisely and precisely in the contracts.

In Replacement of Defensive Coding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In existing Ada code that is migrated to |SPARK|, defensive coding is typically
used to verify the correct integration between components: checks are made at
the start of a subprogram that inputs (parameters and global variables) satisfy
expected properties, and an exception is raised or the program halted if an
unexpected situation is found.

Defensive code can be advantageously replaced by preconditions:

* The dynamic checks performed by defensive code at run time can be performed
  equally by preconditions, and they can be enabled at a much finer grain
  thanks to :ref:`Pragma Assertion_Policy`.

* |GNATprove| can use the preconditions to prove correct integration between
  components, as in new developments.

.. index:: Gold level; functional correctness

Prove Functional Correctness
----------------------------

Functional Correctness In New Developments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove| can be used to prove functional correctness of an implementation
against its specification. This strongest level of verification can be applied
either to specific subprograms, or specific units, or the complete program. For
those subprograms whose functional correctness is to be checked, the user
should:

#. express the specification of the subprogram as a subprogram contract
   (see :ref:`Preconditions` and :ref:`Postconditions`);

#. use |GNATprove| to prove automatically that most checks (including
   contracts) always hold; and

#. address the remaining unproved checks with manual justifications or testing,
   as already discussed in the section on how to :ref:`Prove Absence of
   Run-Time Errors (AoRTE)`.

As more complex contracts are required in general, it is expected that
achieving that strongest level of verification is also more costly than proving
absence of run-time errors. Typically, |SPARK| features like :ref:`Quantified
Expressions` and :ref:`Expression Functions` are needed to express the
specification, and features like :ref:`Loop Invariants` are needed to achieve
automatic proof. See section on :ref:`Writing Contracts for Functional
Correctness` for examples of such contracts, and section on :ref:`How to Write
Loop Invariants` for examples of the required loop invariants.

When the functional specification is expressed as a set of disjoint cases, the
|SPARK| feature of :ref:`Contract Cases` can be used to increase readability
and to provide an automatic means to verify that cases indeed define a
partitioning of the possible operational contexts.

In Replacement of Unit Testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In existing Ada code that is migrated to |SPARK|, unit testing is typically
used to verify functional correctness: actual outputs obtained when calling the
subprogram are compared to expected outputs for given inputs. A `test case`
defines an expected behavior to verify; a `test procedure` implements a `test
case` with specific given inputs and expected outputs.

Test cases can be used as a basis for functional contracts, as they define in
general a behavior for a set of similar inputs. Thus, a set of test cases can
be transformed into :ref:`Contract Cases`, where each case corresponds to a
test case: the test input constraint becomes the guard of the corresponding
case, while the test output constraint becomes the consequence of the
corresponding case.

|GNATprove| can be used to prove this initial functional contract, as in new
developments. Then, cases can be progressively generalized (by relaxing the
conditions in the guards), or new cases added to the contract, until the full
functional behavior of the subprogram is specified and proved.

Ensure Correct Behavior of Parameterized Software
-------------------------------------------------

In some domains (railway, space), it is common to develop software which
depends on parameterization data, which changes from mission to mission. For
example, the layout of railroads or the characteristics of the payload for a
spacecraft are mission specific, but in general do not require developing
completely new software for the mission. Instead, the software may either
depend on data definition units which are subject to changes between missions,
or the software may load at starting time (possibly during `elaboration` in
Ada) the data which defines the characteristics of the mission. Then, the issue
is that a verification performed on a specific version of the software (for a
given parameterization) is not necessarily valid for all versions of the
software. In general, this means that verification has to be performed again
for each new version of the software, which can be costly.

|SPARK| provides a better solution to ensure correct behavior of the software
for all possible parameterizations. It requires defining a getter function for
every variable or constant in the program that represents an element of
parameterization, and calling this getter function instead of reading the
variable or constant directly. Because |GNATprove| performs an analysis based
on contracts, all that is known at analysis time about the value returned by a
getter function is what is available from its signature and
contract. Typically, one may want to use :ref:`Scalar Ranges` or
:ref:`Predicates` to constrain the return subtype of such getter functions, to
reflect the operational constraints respected by all parameterizations.

This technique ensures that the results of applying |GNATprove| are valid not
only for the version of the software analyzed, but for any other version that
satisfies the same operational constraints. This is valid whatever the
objective(s) pursued with the use of |SPARK|: :ref:`Prove Absence of Run-Time
Errors (AoRTE)`, :ref:`Prove Correct Integration Between Components`,
:ref:`Prove Functional Correctness`, etc.

It may be the case that changing constants into functions makes the code
illegal because the constants were used in representation clauses that require
static values. In that case, compilation switch ``-gnatI`` should be specified
when analyzing the modified code with |GNATprove|, so that representation
clauses are ignored. As representation clauses have no effect on |GNATprove|'s
analysis, and their validity is checked by |GNAT Pro| when compiling the
original code, the formal verification results are valid for the original code.

For constants of a non-scalar type (for example, constants of record or array
type), an alternative way to obtain a similar result as the getter function is
to define the constant as a deferred constant, whose initial declaration in the
visible part of a package spec does not specify the value of the
constant. Then, the private part of the package spec which defines the
completion of the deferred constant must be marked ``SPARK_Mode => Off``, so
that clients of the package only see the visible constant declaration without
value. In such a case, the analysis of client units with |GNATprove| is valid
for all possible values of the constant.

.. index:: Silver level; optimize run-time checks

Safe Optimization of Run-Time Checks
------------------------------------

Enabling run-time checks in a program usually increases the running time by
around 10%. This may not fit the timing schedule in some highly constrained
applications. In some cases where a piece of code is called a large number of
times (for example in a loop), enabling run-time checks on that piece of code
may increase the running time by far more than 10%. Thus, it may be tempting to
remove run-time checking in the complete program (with compilation switch
``-gnatp``) or a selected piece of code (with pragma ``Suppress``), for the
purpose of decreasing running time. The problem with that approach is that the
program is not protected anymore against programming mistakes (for safety) or
attackers (for security).

|GNATprove| provides a better solution, by allowing users to prove the absence
of all run-time errors (or run-time errors of a specific kind, for example
overflow checks) in a piece of code, provided the assumptions on which their
proof relies are respected. This includes in particular the fact that the
precondition of the enclosing subprogram is respected. Then, all run-time
checks (or run-time errors of a specific kind) can be suppressed in that piece
of code using pragma ``Suppress``, knowing that they will never fail at run
time, provided the corresponding assumptions are checked. For example, this can
be done for the precondition of the enclosing subprogram by using :ref:`Pragma
Assertion_Policy`. For more details, see :ref:`Choosing Which Run-time Checking
to Keep`. By replacing many checks with a few checks, we can decrease the
running time of the application by doing safe and controlled optimization of
run-time checks.

.. index:: Bronze level; data and control coupling

Address Data and Control Coupling
---------------------------------

As defined in the avionics standard DO-178, data coupling is `"The dependence
of a software component on data not exclusively under the control of that
software component"` and control coupling is `"The manner or degree by which
one software component influences the execution of another software
component"`, where a software component could be a subprogram, a unit or a set
of units.

Although analysis of data and control coupling are not performed at the same
level of details in non-critical domains, knowledge of data and control
coupling is important to assess impact of code changes. In particular, it may
be critical for security that some secret data does not leak publicly, which
can be rephrased as saying that only the specified data dependencies are
allowed. |SPARK| is ideally equipped to support such analysis, with its
detailed :ref:`Subprogram Contracts`:

* With :ref:`Data Dependencies`, a user can specify exactly the input and
  output data of a subprogram, which identifies the `"data not exclusively
  under the control of that software component"`:

  * When taking the subprogram as component, any variable in the data
    dependencies is in general not exclusively under the control of that
    software component.

  * When taking the unit (or sets of units) as component, any variable in the
    data dependencies that is not defined in the unit itself (or the set of
    units) is in general not exclusively under the control of that software
    component.

* With :ref:`Flow Dependencies`, a user can specify the nature of the
  `"dependence of a software component on data not exclusively under the
  control of that software component"`, by identifying how that data may
  influence specific outputs of a subprogram.

* With :ref:`Flow Dependencies`, a user can also specify how `"one software
  component influences the execution of another software component"`, by
  identifying the shared data potentially written by the subprogram.

* With functional contracts (:ref:`Preconditions` and :ref:`Postconditions`), a
  user can specify very precisely the behavior of the subprogram, which defines
  how it `"influences the execution of another software component"`. These
  contracts need not be complete, for example they could describe the
  precedence order rules for calling various subprograms.

When using data and flow dependencies, |GNATprove|'s flow analysis is
sufficient to check that the program implements its specifications. When using
functional contracts, |GNATprove|'s proof should also be applied.

.. index:: portability

Ensure Portability of Programs
------------------------------

Using |SPARK| enhances portability of programs by excluding language features
that are known to cause portability problems, and by making it possible to
obtain guarantees that specific portability problems cannot occur. In
particular, analyses of |SPARK| code can prove the absence of run-time errors
in the program, and that specified functional properties always hold.

Still, porting a |SPARK| program written for a given compiler and target to
another compiler and/or target may require changes in the program. As |SPARK|
is a subset of Ada, and because in general only some parts of a complete
program are in |SPARK|, we need to consider first the issue of portability in
the context of Ada, and then specialize it in the context of |SPARK|.

Note that we consider here portability in its strictest sense, whereby a
program is portable if its observable behavior is exactly the same across a
change of compiler and/or target. In the more common sense of the word, a
program is portable if it can be reused without modification on a different
target, or when changing compiler.  That is consistent with the definition of
portability in WikiPedia: "Portability in high-level computer programming is
the usability of the same software in different environments". As an example of
a difference between both interpretations, many algorithms which use
trigonometry are portable in the more common sense, not in the strictest sense.

Portability of Ada Programs
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Programs with errors cause additional portability issues not seen in programs
without errors, which is why we consider them separately.

Portability of Programs Without Errors
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Ada Reference Manual defines precisely which features of the language
depend on choices made by the compiler (see Ada RM 1.1.3 "Conformity of an
Implementation with the Standard"):

* *Implementation defined behavior* - The set of possible behaviors is
  specified in the language, and the particular behavior chosen in a compiler
  should be documented. An example of implementation defined behavior is the
  size of predefined integer types (like ``Integer``). All implementation
  defined behaviors are listed in Ada RM M.2, and GNAT documents its
  implementation for each of these points in section 7 "Implementation Defined
  Characteristics" of the GNAT Reference Manual.

* *Unspecified behavior* - The set of possible behaviors is specified in the
  language, but the particular behavior chosen in a compiler need not be
  documented. An example of unspecified behavior is the order of evaluation of
  arguments in a subprogram call.

Changes of compiler and/or target may lead to different implementation defined
and unspecified behavior, which may or not have a visible effect. For example,
changing the order of evaluation of arguments in a subprogram call only has a
visible effect if the evaluation of arguments itself has some side-effects.

Section 18.4 "Implementation-dependent characteristics" of the GNAT Reference
Manual gives some advice on how to address implementation defined behavior for
portability.

A particular issue is that the Ada Reference Manual gives much implementation
freedom to the compiler in the implementation of operations of fixed-point and
floating-point types:

* The small of a fixed-point type is implementation defined (Ada RM 3.5.9(8/2))
  unless specified explicitly.

* The base type of a fixed-point type is implementation defined (Ada RM
  3.5.9(12-16)), which has an impact on possible overflows.

* The rounded result of an ordinary fixed-point multiplication or division is
  implementation defined (Ada RM G.2.3(10)).

* For some combinations of types of operands and results for fixed-point
  multiplication and division, the value of the result belongs to an
  implementation defined set of values (Ada RM G.2.3(5)).

* The semantics of operations on floating-point types is implementation defined
  (Ada RM G.2). It may or may not follow the IEEE 754 floating point standard.

* The precision of elementary functions (exponential and trigonometric
  functions) is implementation defined (Ada RM G.2.4).

Section 18.1 "Writing Portable Fixed-Point Declarations" of the GNAT Reference
Manual gives some advice on how to reduce implementation defined behavior for
fixed-point types. Use of IEEE 754 floating-point arithmetic can be enforced in
GNAT by using the compilation switches "-msse2 -mfpmath=sse", as documented in
section 6.3.1.6 "Floating Point Operations" of the |GNAT Pro| User's Guide.

Note that a number of restrictions can be used to prevent some features leading
to implementation defined or unspecified behavior:

* Restriction ``No_Fixed_Point`` forbids the use of fixed-point types.

* Restriction ``No_Floating_Point`` forbids the use of floating-point types.

* Restriction ``No_Implementation_Aspect_Specifications`` forbids the use of
  implementation defined aspects.

* Restriction ``No_Implementation_Attributes`` forbids the use of
  implementation defined attributes.

* Restriction ``No_Implementation_Pragmas`` forbids the use of implementation
  defined pragmas.

.. note::

   SPARK defines a few constructs (aspects, pragmas and attributes) that are
   not defined in Ada. While |GNAT Pro| supports these constructs, care should
   be exercised to use these constructs with other compilers, or older versions
   of |GNAT Pro|. This issue is detailed in section :ref:`Portability Issues`.

Portability of Programs With Errors
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In addition to the portability issues discussed so far, programs with errors
cause specific portability issues related to whether errors are detected and
how they are reported. The Ada Reference Manual distinguishes between four
types of errors (see Ada RM 1.1.5 "Classification of Errors"):

* *Compile-time errors* - These errors make a program illegal, and should be
  detected by any Ada compiler. They do not cause any portability issue, as
  they must be fixed before compilation.

.. index:: run-time error

* *Run-time errors* - These errors are signaled by raising an exception at run
  time. They might be a cause of portability problems, as a change of compiler
  and/or target may lead to new run-time errors. For example, a new compiler
  may cause the program to use more stack space, leading to an exception
  ``Storage_Error``, and a new target may change the size of standard integer
  types, leading to an exception ``Constraint_Error``.

.. index:: bounded error

* *Bounded errors* - These errors need not be detected either at compiler time
  or at run time, but their effects should be bounded. For example, reading an
  uninitialized value may result in any value of the type to be used, or to
  ``Program_Error`` being raised. Like for run-time errors, they might be a
  cause of portability problems, as a change of compiler and/or target may lead
  to new bounded errors.

.. index:: erroneous execution

* *Erroneous execution* - For the remaining errors, a program exhibits
  erroneous execution, which means that the error need not be detected, and
  its effects are not bounded by the language rules. These errors might be a
  cause of portability problems.

Portability issues may arise in a number of cases related to errors:

* The original program has an error that is not detected (a run-time error,
  bounded error or erroneous execution). Changing the compiler and/or target
  causes the error to be detected (an exception is raised) or to trigger a
  different behavior. Typically, reads of uninitialized data or illegal
  accesses to memory that are not detected in the original program may result
  in errors when changing the compiler and/or the target.

* The original program has no error, but changing the compiler and/or target
  causes an error to appear, which may or not be detected. Typically, uses of
  low-level constructs like ``Unchecked_Conversion`` which depend on the exact
  representation of values in bits may lead to errors when changing the
  compiler and/or the target. Some run-time errors like overflow errors or
  storage errors are also particularly sensitive to compiler and target
  changes.

To avoid portability issues, errors should be avoided by using suitable
analyses and reviews in the context of the original and the new compiler and/or
target. Whenever possible, these analyses and reviews should be automated by
tools to guarantee that all possible errors of a given kind have been reported.

Benefits of Using SPARK for Portability
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The :ref:`Language Restrictions` in |SPARK| favor portability by excluding
problematic language features (see :ref:`Excluded Ada Features`):

* By excluding side-effects in expressions, |SPARK| programs cannot suffer from
  effects occurring in different orders depending on the order of evaluation of
  expressions chosen by the compiler.

* By excluding aliasing, the behavior of |SPARK| programs does not depend on
  the parameter passing mechanism (by copy or by reference) or the order of
  assignment to out and in-out parameters passed by copy after the call, which
  are both chosen by the compiler.

* By excluding controlled types, |SPARK| programs cannot suffer from the
  presence and ordering of effects taking place as part of the initialization,
  assignment and finalization of controlled objects, which depend on choices
  made by the compiler.

As permitted by the |SPARK| language rules (see section 1.4.1 "Further Details
on Formal Verification" of the SPARK Reference Manual), |GNATprove| rejects
with an error programs which may implicitly raise a ``Program_Error`` in parts
of code that are in |SPARK|. For example, all static execution paths in a
|SPARK| function should end with a return statement, a raise statement, or a
``pragma Assert (False)``. |GNATprove|'s analysis can be further used to ensure
that dynamic executions can only end in a return.

|GNATprove| reduces portability issues related to the use of fixed-point and
floating-point values:

* |GNATprove| supports a subset of fixed-point types and operations that
  ensures that the result of an operation always belongs to the *perfect result
  set* as defined in Ada RM G.2.3. Note that the perfect result set still
  contains in general two values (the two model fixed-point values above and
  below the perfect mathematical result), which means that two compilers may
  give two different results for multiplication and division. Users should thus
  avoid multiplication and division of fixed-point values for maximal
  portability. See :ref:`GNATprove Limitations`.

* |GNATprove| assumes IEEE 754 standard semantics for basic operations of
  floating-point types (addition, subtraction, multiplication, division). With
  GNAT, this is achieved by using compilation switches
  "-msse2 -mfpmath=sse". Users should still avoid elementary functions
  (exponential and trigonometric functions) for maximal portability. See
  :ref:`Semantics of Floating Point Operations`.

Additionally, |GNATprove| can detect all occurrences of specific portability
issues in |SPARK| code (that is, parts of the program for which
``SPARK_Mode=On`` is specified, see section on :ref:`Identifying SPARK Code`)
when run in specific modes (see :ref:`Effect of Mode on Output` for a
description of the different modes):

* In all modes (including mode ``check``), when switch ``--pedantic`` is set,
  |GNATprove| issues a warning for every arithmetic operation which could be
  re-ordered by the compiler, thus leading to a possible overflow with one
  compiler and not another. For example, arithmetic operation ``A + B + C`` can
  be interpreted as ``(A + B) + C`` by one compiler, and ``A + (B + C)`` (after
  re-ordering) by another compiler. Note that GNAT always uses the former
  version without re-ordering. See :ref:`Parenthesized Arithmetic Operations`.

* In modes ``flow``, ``prove`` and ``all``, |GNATprove| issues high check
  messages on possible parameter aliasing, when such an aliasing may lead to
  interferences. This includes all cases where the choice of parameter passing
  mechanism in a compiler (by copy or by reference) might influence the
  behavior of the subprogram. See :ref:`Absence of Interferences`.

* In modes ``flow``, ``prove`` and ``all``, |GNATprove| issues check messages
  on possible reads of uninitialized data. These messages should be reviewed
  with respect to the stricter :ref:`Data Initialization Policy` in |SPARK|
  rather than in Ada. Hence, it is possible when the program does not conform
  to the stricter |SPARK| rules to manually validate them, see section
  :ref:`Justifying Check Messages`.

* In modes ``prove`` and ``all``, |GNATprove| issues check messages on all
  possible run-time errors corresponding to raising exception
  ``Constraint_Error`` at run time, all possible failures of assertions
  corresponding to raising exception ``Assert_Error`` at run time, and all
  possible explicit raising of unexpected exceptions in the program.

The analysis of |GNATprove| can take into account characteristics of the target
(size and alignment of standard scalar types, endianness) by specifying a
:ref:`Target Parameterization`.

How to Use |SPARK| for Portability
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|GNATprove|'s analysis may be used to enhance the portability of programs. Note
that the guarantees provided by this analysis only hold for the source
program. To ensure that these guarantees extend to the executable object code,
one should independently provide assurance that the object code correctly
implements the semantics of the source code.

Avoiding Non-Portable Features
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As much as possible, uses of non-portable language features should be avoided,
or at least isolated in specific parts of the program to facilitate analyses
and reviews when changing the compiler and/or the target.

This includes in particular language features that deal with machine addresses,
data representations, interfacing with assembler code, and similar issues (for
example, language attribute ``Size``). When changing the compiler and/or the
target, the program logic should be carefully reviewed for possible dependences
on the original compiler behavior and/or original target characteristics. See
also the section 18.4.5 "Target-specific aspects" of the GNAT Reference
Manual.

In particular, features that bypass the type system of Ada for reinterpreting
values (``Unchecked_Conversion``) and memory locations (``Address`` clause
overlays, in which multiple objects are defined to share the same address,
something that can also be achieved by sharing the same ``Link_Name`` or
``External_Name``) have no impact on |SPARK| analysis, yet they may lead to
portability issues.

By using the following restrictions (or a subset thereof), one can ensure that
the corresponding non-portable features are not used in the program:

.. code-block:: ada

   pragma No_Dependence (Ada.Unchecked_Conversion);
   pragma No_Dependence (System.Machine_code);

Similarly, the program logic should be carefully reviewed for possible
dependency on target characteristics (for example, the size of standard integer
types). |GNATprove|'s analysis may help here as it can take into account the
characteristics of the target. Hence, proofs of functional properties with
|GNATprove| ensure that these properties will always hold on the target.

In the specific case that the target is changing, it might be useful to run
|GNATprove|'s analysis on the program in ``proof`` mode, even if it cannot
prove completely the absence of run-time errors and that the specified
functional properties (if any) hold. Indeed, by running |GNATprove| twice, once
with the original target and once with the new target, comparing the results
obtained in both cases might point to parts of the code that are impacted by
the change of target, which may require more detailed manual reviews.

Apart from non-portable language features and target characteristics,
non-portability in |SPARK| may come from a small list of causes:

* Possible re-ordering of non-parenthesized arithmetic operations. These can be
  detected by running |GNATprove| (see :ref:`Benefits of Using SPARK for
  Portability`). Then, either these operations may not be re-ordered by the
  compiler (for example, GNAT ensures this property), or re-ordering may not
  lead to an intermediate overflow (for example, if the base type is large
  enough), or the user may introduce parentheses to prevent re-ordering.

* Possible aliasing between parameters (or parameters and global variables) of
  a call causing interferences.  These can be detected by running |GNATprove|
  (see :ref:`Benefits of Using SPARK for Portability`). Then, either aliasing
  is not possible in reality, or aliasing may not cause different behaviors
  depending on the parameter passing mechanism chosen in the compiler, or the
  user may change the code to avoid aliasing. When |SPARK| subprograms are
  called from non-|SPARK| code (for example Ada or C code), manual reviews
  should be performed to ensure that these calls cannot introduce aliasing
  between parameters, or between parameters and global variables.

* Possible different choices of base type for user-defined integer types
  (contrary to derived types or subtypes, which inherit their base type from
  their parent type). |GNATprove| follows |GNAT Pro| in choosing as base type
  the smallest multiple-words-size integer type that contains the type
  bounds (see :ref:`Base Type of User-Defined Integer Types` for more
  information).

* Issues related to errors. See section :ref:`Avoiding Errors to Enhance
  Portability`.

* Issues related to the use of fixed-point or floating-point operations. See
  section :ref:`Portability of Fixed-Point and Floating-Point Computations`
  below.

Avoiding Errors to Enhance Portability
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Because errors in a program make portability particularly challenging (see
:ref:`Portability of Programs With Errors`), it is important to ensure that a
program is error-free for portability. |GNATprove|'s analysis can help by
ensuring that the |SPARK| parts of a program are free from broad kinds of
errors:

* all possible reads of uninitialized data

* all possible explicit raise of unexpected exceptions in the program

* all possible run-time errors except raising exception ``Storage_Error``,
  corresponding to raising exception ``Program_Error``, ``Constraint_Error`` or
  ``Tasking_Error`` at run time

* all possible failures of assertions corresponding to raising exception
  ``Assert_Error`` at run time

When parts of the program are not in |SPARK| (for example, in Ada or C), the
results of |GNATprove|'s analysis depend on assumptions on the correct behavior
of the non-|SPARK| code. For example, callers of a |SPARK| subprogram should
only pass initialized input values, and non-|SPARK| subprograms called from
|SPARK| code should respect their postcondition. See section :ref:`Managing
Assumptions` for more details on assumptions.

In particular, when changing the target characteristics, |GNATprove|'s analysis
can be used to show that no possible overflow can occur as a result of changing
the size of standard integer types.

|GNATprove|'s analysis does not detect possible run-time errors corresponding
to raising exception ``Storage_Error`` at run time, which should be
independently assessed.

Portability of Fixed-Point and Floating-Point Computations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Portability issues related to the use of fixed-point or floating-point
operations can be avoided altogether by ensuring that the program does not use
fixed-point or floating-point values, using:

.. code-block:: ada

   pragma Restrictions (No_Fixed_Point);
   pragma Restrictions (No_Floating_Point);

When fixed-point values are used, the value of the small and size in bits for
the type should be specified explicitly, as documented in section 18.1 "Writing
Portable Fixed-Point Declarations" of the GNAT Reference Manual:

.. code-block:: ada

   My_Small : constant := 2.0**(-15);
   My_First : constant := -1.0;
   My_Last  : constant := +1.0 - My_Small;

   type F2 is delta My_Small range My_First .. My_Last;
   for F2'Small use my_Small;
   for F2'Size  use 16;

The program should also avoid multiplication and division of fixed-point values
to ensure that the result of arithmetic operations is exactly defined.

When floating-point values are used, use of IEEE 754 standard semantics for
basic operations of floating-point types (addition, subtraction,
multiplication, division) should be enforced. With GNAT, this is achieved by
using compilation switches "-msse2 -mfpmath=sse".

The program should also avoid elementary functions (exponential and
trigonometric functions), which can be ensured with a restriction:

.. code-block:: ada

   pragma No_Dependence (Ada.Numerics);

If elementary functions are used, subject to reviews for ensuring portability,
|GNATprove|'s proof results may depend on the fact that elementary functions
can be modeled as mathematical functions of their inputs that always return
the same result when taking the same values in arguments. GNAT compiler was
modified to ensure this property (see https://blog.adacore.com/how-our-compiler-learnt-from-our-analyzers),
which may not hold for other Ada compilers.

Project Scenarios
=================

The workflow for using |SPARK| depends not only on the chosen :ref:`Objectives
of Using SPARK`, but also on the context in which |SPARK| is used: Is it for a
new development? Or an evolution of an existing codebase? Is the existing
codebase in Ada or in a version of SPARK prior to SPARK 2014? We examine all
these project scenarios in this section.

.. index:: migration from Ada; project scenario

Maintenance and Evolution of Existing Ada Software
--------------------------------------------------

Although |SPARK| is a large subset of Ada, it contains a number of
:ref:`Language Restrictions` which prevent in general direct application of
|GNATprove| to an existing Ada codebase without any modifications. The
suggested workflow is to:

#. Identify violations of |SPARK| restrictions.
#. For each violation, either rewrite the code in |SPARK| or mark it
   ``SPARK_Mode => Off`` (see section on :ref:`Identifying SPARK Code`).
#. Perform the required analyses to achieve the desired objectives (see section
   on :ref:`Formal Verification with GNATprove`), a process which likely
   involved writing contracts (see in particular section on :ref:`How to Write
   Subprogram Contracts`).
#. Make sure that the assumptions made for formal verification are justified at
   the boundary between |SPARK| and full Ada code (see section on
   :ref:`Managing Assumptions`).

Identifying Violations of |SPARK| Restrictions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A simple way to identify violations of |SPARK| restrictions is by :ref:`Setting
the Default SPARK_Mode` to ``SPARK_Mode => On``, and then running |GNATprove|
either in ``check`` mode (to report basic violations) or in ``flow`` mode (to
report violations whose detection requires flow analysis).

If only a subset of the project files should be analyzed, one should create a
project file for :ref:`Specifying Files To Analyze` or :ref:`Excluding Files
From Analysis`.

Finally, one may prefer to work her way through the project one unit at a time
by :ref:`Using SPARK_Mode in Code`, and running |GNATprove| on the current unit
only.

Rewriting the Code in |SPARK|
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Depending on the violation, it may be more or less easy to rewrite the code in
|SPARK|:

* Unsupported types should in general be rewritten as private types of a
  package whose public part is marked ``SPARK_Mode => On`` and whose private
  part is marked ``SPARK_Mode => Off``. Thus, the body of that package cannot be
  analyzed by |GNATprove|, but clients of the package can be analyzed.

* Functions with side-effects should be rewritten as procedures, by adding an
  additional out parameter for the result of the function.

* Aliasing should be either explicitly signed off by :ref:`Justifying Check
  Messages` or removed by introducing a copy of the object to pass as argument
  to the call.

* Controlled types cannot be rewritten easily.

.. _Using SPARK_Mode to Select or Exclude Code:

Using ``SPARK_Mode`` to Select or Exclude Code
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Depending on the number and location of remaining violations, ``SPARK_Mode``
can be used in different ways:

* If most of the codebase is in |SPARK|, :ref:`Setting the Default SPARK_Mode`
  to ``SPARK_Mode => On`` is best. Violations should be isolated in parts of
  the code marked ``SPARK_Mode => Off`` by either :ref:`Excluding Selected Unit
  Bodies` or :ref:`Excluding Selected Parts of a Unit`.

* Otherwise, ``SPARK_Mode => On`` should be applied selectively for
  :ref:`Verifying Selected Subprograms` or :ref:`Verifying Selected
  Units`. Violations are allowed outside the parts of the code marked
  ``SPARK_Mode => On``.

* Even when most of the code is in |SPARK|, it may be more cost effective to
  apply ``SPARK_Mode => On`` selectively rather than by default. This is the
  case in particular when some units have non-|SPARK| declarations in the
  public part of their package spec.
  Rewriting the code of these units to isolate the non-|SPARK|
  declarations in a part that can be marked ``SPARK_Mode => Off`` may be more
  costly than specifying no ``SPARK_Mode`` for these units, which allows
  |SPARK| code elsewhere in the program to refer to the |SPARK| entities in
  these units.

When analyzing a unit for the first time, it may help to gradually mark the
code ``SPARK_Mode => On``:

#. Start with the unit spec marked ``SPARK_Mode => On`` and the unit body
   marked ``SPARK_Mode => Off``. First run |GNATprove| in ``flow`` mode, then
   in ``proof`` mode, until all errors are resolved (some unproved checks may
   remain, as errors and checks are different :ref:`Categories of Messages`).

#. Continue with the both the unit spec and body marked ``SPARK_Mode =>
   On``. First run |GNATprove| in ``flow`` mode, then in ``proof`` mode, until
   all errors are resolved.

#. Now that |GNATprove| can analyze the unit without any errors, continue with
   whatever analysis is required to achieve the desired objectives.

Choosing Which Run-time Checking to Keep
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Inside proven |SPARK| code, no run-time errors of the kinds that |GNATprove|
targets can be raised (see :ref:`Avoiding Errors to Enhance Portability` for
details), provided the analysis assumptions are respected. See section
:ref:`Managing Assumptions` for more details on assumptions. In such proven
code, it is possible to remove run-time checking as described in section
:ref:`Safe Optimization of Run-Time Checks`.

Note that |GNATprove|'s analysis does not detect possible run-time errors
corresponding to raising exception ``Storage_Error`` at run time. As described
in "GNAT User's Guide for Native Platforms", section 6.6.1 on "Stack Overflow
Checking", ``gcc`` option ``-fstack-check`` can be used to activate stack
checking.

An important use case is the one of unproven code calling proven code, typically
when rewriting core components of the application in |SPARK|. In that case, the
guarantees provided by proof on |SPARK| code rely on the following main
assumptions:

- The preconditions of proven |SPARK| subprograms should be respected. If these
  subprograms can be called from subprograms that are not proved, it is
  recommended to activate their preconditions at run time with :ref:`Pragma
  Assertion_Policy`, as shown in :ref:`Writing Contracts for Program
  Integrity`.

- All inputs of proven |SPARK| subprograms should have valid values for their
  types. This is enforced by the combination of flow analysis and proof in
  |SPARK| code, both for parameters and global variables that are read in the
  subprogram. It can be partially verified (for parameters but not global
  variables) during testing for calls from unproven subprograms by compiling
  the program with special switches to add run-time checks related to validity,
  as described in section :ref:`Between Proof and Unit Testing`.

- Inputs and outputs that may interfere should not be aliased. See section
  :ref:`Absence of Interferences` for details. Similar to validity, it can be
  partially verified (for parameters but not global
  variables) during testing for calls from unproven
  subprograms by compiling the program with special switch ``-gnateA``, as
  described in section :ref:`Between Proof and Unit Testing`.

Inside unproven code, users may opt for keeping run-time checking and/or
assertion checking in the executable or not, depending on their overall error
detection and recovery policy. At the level of a compilation unit, this choice
can be made through compilation switch ``-gnatp`` (for suppressing run-time
checking) and ``-gnata`` (for activating assertion checking). These choices can
be reversed for a selected piece of code with pragmas ``Suppress`` and
``Unsuppress`` (for all checks) and ``Assertion_Policy`` (for assertions only).

Additional compilation switches that activate validity checking are best kept
for verification, as described in section :ref:`Between Proof and Unit
Testing`. Activating them in the final executable may lead to large increases
in running time, with some checks being inserted at unexpected/extra places, as
these validity checks do not follow a formal definition like the one found in
Ada Reference Manual for other run-time checks.

New Developments in SPARK
-------------------------

In this scenario, a significant part of a software (possibly a module, possibly
the whole software) is developed in |SPARK|. Typically, |SPARK| is used for the
most critical parts of the software, with less critical parts programmed in
Ada, C or Java (for example the graphical interface). A typical development
process for this scenario might be:

#. Produce the high level (architectural) design in terms of package
   specifications. Determine which packages will be in |SPARK|, to be marked
   ``SPARK_Mode => On``.

#. Alternatively, if the majority of packages are to be |SPARK|, :ref:`Setting
   the Default SPARK_Mode` to ``SPARK_Mode => On`` is best. Those few units
   that are not |SPARK| should be marked ``SPARK_Mode => Off``.

#. Add :ref:`Package Contracts` to |SPARK| packages and, depending on the
   desired objectives, add relevant :ref:`Subprogram Contracts` to the
   subprograms declared in these packages. The package contracts should
   identify the key elements of :ref:`State Abstraction` which might also be
   referred to in :ref:`Data Dependencies` and :ref:`Flow Dependencies`.

#. Begin implementing the package bodies. One typical method of doing this is
   to use a process of top-down decomposition, starting with a top-level
   subprogram specification and implementing the body by breaking it down into
   further (nested) subprograms which are themselves specified but not yet
   implemented, and to iterate until a level is reached where it is appropriate
   to start writing executable code. However the exact process is not mandated
   and will depend on other factors such as the design methodology being
   employed. Provided unimplemented subprograms are stubbed (that is, they are
   given dummy bodies), |GNATprove| can be used at any point to analyze the
   program.

#. As each subprogram is implemented, |GNATprove| can be used (in mode ``flow``
   or ``proof`` depending on the objectives) to verify it (against its
   contract, and/or to show absence of run-time errors).

.. index:: migration from SPARK 2005; project scenario

Conversion of Existing SPARK Software to SPARK 2014
---------------------------------------------------

If an existing piece of software has been developed in a previous version of
|SPARK| and is still undergoing active development/maintenance then it may be
advantageous to upgrade to using SPARK 2014 in order to make use of the larger
language subset and the new tools and environment. This requires more efforts
than previous upgrades between versions of |SPARK| (SPARK 83, SPARK 95 and
SPARK 2005) because the new version SPARK 2014 of |SPARK| is incompatible with
those previous versions of the language. While the programming language itself
in those previous versions of SPARK is a strict subset of SPARK 2014, the
contracts and assertions in previous versions of SPARK are expressed as
stylized comments that are ignored by |GNATprove|. Instead, those contracts and
assertions should be expressed as executable Ada constructs, as presented in
the :ref:`Overview of SPARK Language`.

The |SPARK| Language Reference Manual has an appendix containing a `SPARK 2005
to SPARK 2014 Mapping Specification` which can be used to guide the conversion
process. Various options can be considered for the conversion process:

#. `Only convert annotations into contracts and assertions, with minimal
   changes to the executable code` - Note that some changes to the code may be
   required when converting annotations, for example adding with-clauses in a
   unit to give visibility over entities used in contracts in this unit but
   defined in another units (which was performed in previous versions of
   |SPARK| with ``inherit`` annotations). This conversion should be relatively
   straightforward by following the mapping of features between the two
   languages.

   The |SPARK| tools should be used to analyze the work in progress throughout
   the conversion process (which implies that a bottom-up approach may work
   best) and any errors corrected as they are found. This may also be an
   occasion to dramatically simplify annotations, as |GNATprove| requires far
   fewer of them. See the README of the SPARKSkein program distributed with SPARK.

   Once the conversion is complete, development and maintenance can continue in
   |SPARK|.

#. `In addition to converting annotations, benefit from the larger language and
   more powerful tools to simplify code and contracts` - SPARK 2014 is far less
   constraining than previous versions of |SPARK| in terms of dependencies
   between units (which can form a graph instead of a tree), control structures
   (for example arbitrary return statements and exit statements are allowed),
   data structures (for example scalar types with dynamic bounds are allowed),
   expressions (for example local variables can be initialized with non-static
   expressions at declaration). In addition, useful new language constructs are
   available:

   * :ref:`Contract Cases` can be used to replace complex postconditions with
     implications.

   * :ref:`Predicates` can be used to state invariant properties of subtypes, so
     that they need not be repeated in preconditions, postconditions, loop
     invariants, etc.

   * :ref:`Expression Functions` can be used to replace simple query functions
     and their postcondition.

   * :ref:`Ghost Code` can be used to mark code only used for verification.

   * :ref:`Loop Variants` can be used to prove the termination of loops.

   Changing the code to use these new features may favor readability and
   maintenance. These changes can be performed either while converting
   annotations, or as a second stage after all annotations have been converted
   (the case discussed above). Like in the previous case, the |SPARK| tools
   should be used to analyze the work in progress throughout the conversion
   process (which implies that a bottom-up approach may work best) and any
   errors corrected as they are found. Once the conversion is complete,
   development and maintenance can continue in |SPARK|.

#. `Gradually convert annotations and code` - It is possible to keep
   annotations in comments for the previous versions of |SPARK| while gradually
   adding contracts and assertions in SPARK 2014. The latest version of the
   SPARK 2005 toolset facilitates this gradual migration by ignoring |SPARK|
   pragmas. Thus, new contracts (for example :ref:`Preconditions` and
   :ref:`Postconditions`) should be expressed as pragmas rather than aspects in
   that case.

   Typically, annotations and code would be converted when it needs to be
   changed. The granularity of how much code needs to be converted when a
   module is touched should be considered, and is likely to be at the level of
   the whole package.

   The latest version of the SPARK 2005 toolset can be used to continue
   analyzing the parts of the program that do not use the new features of SPARK
   2014, including units which have the two versions of contracts in
   parallel. |GNATprove| can be used to analyze parts of the program that have
   contracts in SPARK 2014 syntax, including units which have the two versions
   of contracts in parallel.

Note that some users may wish to take advantage of the new |SPARK| contracts
and tools whilst retaining the more restrictive nature of SPARK 2005. (Many of
the restrictions from SPARK 2005 have been lifted in |SPARK| because
improvements in the tools mean that sound analysis can be performed without
them, but some projects may need to operate in a more constrained environment.)
This can be achieved using ``pragma Restrictions (SPARK_05)``. For further
details of this restriction please see the GNAT Reference Manual.

Analysis of Frozen Ada Software
-------------------------------

In some very specific cases, users may be interested in the results of
|GNATprove|'s analysis on an unmodified code. This may be the case for example
if the only objective is to :ref:`Ensure Portability of Programs` for existing
Ada programs that cannot be modified (due to some certification or legal
constraints).

In such a case, the suggested workflow is very similar to the one described for
:ref:`Maintenance and Evolution of Existing Ada Software`, except the code
cannot be rewritten when a violation of |SPARK| restrictions is encountered,
and instead that part of the code should be marked ``SPARK_Mode => Off``. To
minimize the parts of the code that need to be marked ``SPARK_Mode => Off``, it
is in general preferable to apply ``SPARK_Mode => On`` selectively rather than
by default, so that units that have non-|SPARK| declarations in the public part
of their package spec need not be marked ``SPARK_Mode => Off``. See
:ref:`Using SPARK_Mode to Select or Exclude Code` for details.


Dealing with Storage_Error
--------------------------

As mentioned, SPARK analysis doesn't cover the possible exhaustion of data
storage, either by exhausting the stack (this can happen by placing too much
data on the stack, or via a too deep recursion) or by exhausting the heap (this
can happen by allocating too much data using ``new``).

To protect against stack exhaustion, we recommend using GNATstack.

As GNATstack doesn't analyze the secondary stack, if protection against
exhaustion of the secondary stack is desired, we recommend using ``pragma
Restrictions (No_Secondary_Stack);``.

To protect against heap exhaustion, a possible way is to encapsulate
allocations in a wrapper that handles the possible ``Storage_Error`` exception
and signals the failure of the allocation to the calling environment via a
return type.  The verification of this wrapper cannot be effectively done with
SPARK as the handler would be considered unreachable. The
following example, inspired by `this Stackoverflow post
<https://stackoverflow.com/questions/67806008/how-to-check-for-storage-error-in-spark-ada>`_
shows such a wrapper, that returns an "invalid" pointer that can't be
dereferenced in case of memory exhaustion:

.. literalinclude:: /examples/ug__storage_error/storage.ads
   :language: ada

.. literalinclude:: /examples/ug__storage_error/storage.adb
   :language: ada

Best Practices
==============

Some commonly used patterns are known to stretch the limits of the |SPARK|
language and toolset. We explain here the various possibilities for handling
them in practice.

Logging
-------

Following the :ref:`Data Initialization Policy` of SPARK, data used for logging
constitutes a global state that all subprograms performing logging should use
explicitly or implicitly with mode ``In_Out`` - it is partially written by the
subprogram - as exemplified below.

.. code-block:: ada

  procedure Do_Something with
    Global => (In_Out => Logging_Data);

  function Compute_Something return T with
    Side_Effects,
    Global => (In_Out => Logging_Data);

However, this behavior can be quite cumbersome. First, it pollutes the
``Global`` contracts, if the user wants to write them, as the effect of the
logging data is generally common to all subprograms and not of interest for the
functional behavior of the program. Second, and more importantly, it forces the
user to turn all functions that perform logging into effectful functions, like
``Compute_Something`` above. Indeed, by default, functions are not allowed to
have side-effects - writing to global data for example - in |SPARK|. Functions
that have such a behavior need to be annotated with the
:ref:`aspect Side_Effects` and have heavy restrictions regarding where they can
be called.

To alleviate these difficulties, it is possible to hide the effect of logging
from the |GNATprove| tool. This can be done by introducing one or several
logging procedures with an explicit ``Global`` contract hiding their effect.
As an example, the ``Do_Log`` procedure below hides the effect of a call to
``Real_Do_Log``. If its body is verified by |GNATprove|, a failed check will be
emitted for the ``Global`` contract of ``Do_Log``. This check can be accepted
using :ref:`Direct Justification with Pragma Annotate` or the body of ``Do_Log``
can be excluded from analysis using pragma or aspect ``SPARK_Mode``, see
:ref:`Identifying SPARK Code`. In the rest of the program, the effect of logging
will be ignored. For example, |GNATprove| will be able to verify the
``Do_Something`` procedure without any complaint.

.. code-block:: ada

   package Logging is
      procedure Do_Log (Msg : String) with
        Global => null;
      --  Logging function with no visible effect
   end Logging;

   package body Logging is
      procedure Real_Do_Log (Msg : String) with
        Global => (In_Out => Logging_Data);
      --  Real logging function with an effect on Logging_Data

      procedure Do_Log (Msg : String) is
      begin
         Real_Do_Log (Msg);
      end Do_Log;
   end Logging;

   procedure Do_Something with
     Global => null
   is
   begin
      Logging.Do_Log ("foo");
   end Do_Something;

.. warning::

  Since part of the code is hidden from analysis or a check is justified, it is
  important to make sure that the rest of the analysis remains sound. In this
  particular case, there should be *no subprogram visible from the program being
  analyzed that reads, directly or indirectly, the value of the logging data*.
  If such a read cannot be avoided, the input should be marked as volatile with
  asynchronous writers (see :ref:`Properties of Volatile Variables`), and the
  missing dependency should be taken into account if information flow is of
  interest (see :ref:`Flow Dependencies`).


Reads From Machine Representation
---------------------------------

To read (and possibly write) data efficiently in memory, it is possible in full
Ada to reinterpret it as the machine representation of typed data. This can be
done either through unchecked conversions, possibly of access types, to avoid
copies, or through address clauses. These two features can also be used in
|SPARK| for this purpose, but with a number of restrictions in particular
related to :ref:`Data Validity` and some level of imprecision.

Unchecked conversions cannot be applied on access types nor on types with
discriminants. Using them might therefore involve copies, even if constant
propagation in the compiler should get rid of most of them. Note that |SPARK|
does not allow for unused bits in the representation of data used as a
source of an unchecked conversion. This is not a problem when reading from an
untyped memory segment, as demonstrated by ``To_Unused_Bits`` below, but could
impact writes. By default, |GNATprove| also ensures that the target type of
unchecked conversion cannot have invalid values. This can be avoided by using
the :ref:`Aspect Potentially_Invalid` as demonstrated on ``To_Invalid_Values``.
Note that |GNATprove| will emit validity checks whenever the result of such a
conversion is read instead:

.. code-block:: ada

   type Bit_Array is array (Positive range <>) of Boolean;
   type Bit_Array_64 is new Bit_Array (1 .. 64) with Pack;

   type Unused_Bits is record
      F : Integer;
   end record with
     Size => 64;
   for Unused_Bits use record
      F at 0 range 0 .. 31;
   end record;

   function To_Unused_Bits is new Ada.Unchecked_Conversion
     (Bit_Array_64, Unused_Bits);

   type Invalid_Values is record
      G1 : Positive;
      G2 : Integer;
   end record with
     Size => 64;

   function To_Invalid_Values is new Ada.Unchecked_Conversion
     (Bit_Array_64, Invalid_Values)
   with Potentially_Invalid;

Note that the result of an unchecked conversion is not always known precisely
by the verification tool, depending on the complexity of the source and target
types.

Like in full Ada, address clauses can be used instead of unchecked conversion in
|SPARK|. Objects with address clauses are only supported by |GNATprove| if
they use an address clause of the form ``with Address => Y'Address`` where
``Y`` is an object. This particular pattern is called an `overlay`.
Other address clauses are handled as :ref:`Volatile Variables`,
and imply a number of additional assumptions that need to be discharged
manually. The restrictions imposed by |SPARK| on overlays are similar to those
on unchecked conversions, except that the conversion is considered to be
bidirectional if the overlay is mutable (both objects are variable), so both
objects need to have neither invalid values nor unused bits (see
:ref:`Data Validity`). If the overlay is constant (both objects are constant)
then these restrictions are relaxed on the overlaying object, making it possible
to use overlays to read untyped memory segments:

.. code-block:: ada

   procedure Parse_Unused_Bits (X : aliased Bit_Array_64) is
      Z : aliased constant Unused_Bits with
        Import,
        Address => X'Address;
   begin
      if Z.F = 0 then
         null;
      end if;
   end Parse_Unused_Bits;

   procedure Parse_Invalid_Values (X : aliased Bit_Array_64) is
      Z : aliased constant Invalid_Values with
        Import,
        Address => X'Address,
        Potentially_Invalid;

   begin
      if Z.G2 = 0 then
         null;
      end if;

      --  Z.G1 might have invalid values, so its validity shall be verified
      if Z.G1'Valid and then Z.G1 = 0 then
         null;
      end if;
   end Parse_Invalid_Values;

Note that it is possible to create a constant overlay on a variable by passing
it as a parameter of mode ``in`` to a subprogram. In the same way, it is
possible to create an overlay with a part of an object by passing it as a
parameter (of mode ``in`` or ``in out``) to a subprogram. For example, we could
call ``Parse_Invalid_Values`` on a variable or a component of an object. Also
note that, currently, the value of overlaid objects is not tracked precisely by
|GNATprove|.

All the possibilities discussed above have limitations and are sometimes
imprecisely handled by |GNATprove|. Instead, it is possible to exclude from
analysis a part of the program using pragma or aspect ``SPARK_Mode``, see
:ref:`Identifying SPARK Code`. If this is done, care should be taken to avoid
breaking the assumption made by the tool on the rest of the program (see
:ref:`Managing Assumptions`), in particular with respect to data validity and
volatility. As an example, the ``Machine_Representation_Access`` generic
package can be a safe way to encapsulate an unsupported overlay, provided ``T``
does not contain subcomponents of an access type:

.. code-block:: ada

   generic
      type T is private;
      Size : Natural;
   package Machine_Representation_Access is
      type Bit_Array is array (Positive range 1 .. Size) of Boolean with Pack;
      pragma Compile_Time_Error
        (Bit_Array'Object_Size /= T'Object_Size, "object sizes should match");

      function Is_Valid (X : Bit_Array) return Boolean with
        Ghost,
        Import,
        Global => null;

      function Model (X : Bit_Array) return T with
        Ghost,
        Import,
        Global => null,
        Pre    => Is_Valid (X);

      function Constant_Reference
        (X : aliased Bit_Array) return not null access constant T
      with
        Pre    => Is_Valid (X),
        Post   => Constant_Reference'Result.all = Model (X),
        Global => null;

      function At_End (X : Bit_Array) return Bit_Array is (X) with
        Ghost,
        Annotate => (GNATprove, At_End_Borrow);

      function At_End (X : access constant T) return access constant T is (X)
      with
        Ghost,
        Annotate => (GNATprove, At_End_Borrow);

      function Reference
        (X : aliased in out Bit_Array) return not null access T
      with
        Pre    => Is_Valid (X),
        Post   => Is_Valid (At_End (X))
        and then At_End (Reference'Result).all = Model (At_End (X)),
        Global => null;
   end Machine_Representation_Access;

   package body Machine_Representation_Access with
     SPARK_Mode => Off
   is
      function Constant_Reference
        (X : aliased Bit_Array) return not null access constant T
      is
         Z : aliased constant T with Import, Address => X'Address;
      begin
         return Z'Unchecked_Access;
      end Constant_Reference;

      function Reference
        (X : aliased in out Bit_Array) return not null access T
      is
         Z : aliased T with Import, Address => X'Address;
      begin
         return Z'Unchecked_Access;
      end Reference;
   end Machine_Representation_Access;

The ``Constant_Reference`` and ``Reference`` functions are
:ref:`Traversal Functions`. They can be used to read and potentially modify
their parameter as a value of type ``T`` using local observers or borrowers as
in the following example:

.. code-block:: ada

   declare
      Y : access T := Reference (X);
   begin
      Y.F1 := 13;
   end;
   pragma Assert (Constant_Reference (X).F1 = 13);

Note that, in this example, ``Is_Valid`` and ``Model`` are
:ref:`Non-Executable Ghost Code`, so they can only be used in disabled ghost
code and assertions, and not directly in the program. If a definition or a
contract is given for these functions for some value of ``T``, it is necessary
to make sure that it matches their expected semantics. In particular,
``Is_Valid`` shall return True if and only if its parameter is a representation
is a valid value of type ``T``.

Pointer-Based Data Structures
-----------------------------

The :ref:`SPARK Libraries` offers a variety of containers that can be used to
construct data-structures in a |SPARK|-compliant way. If it is possible, using
such containers instead of a pointer-based data structure might be the easiest
way forward. As the API of formal containers (see
:ref:`Formal Containers Library`) is sometimes heavy, it can be better to
wrap the instance in a package in order to offer a simplified API instead.
As an example, the package ``My_Integer_Sets`` below uses formal hashed sets to
implement a set of small integers:

.. literalinclude:: /examples/ug__container_wrapper/my_integer_sets.ads
   :language: ada

Access types are supported in |SPARK| but they should comply with a strict
:ref:`Memory Ownership Policy` to ensure :ref:`Absence of Interferences`. In
particular, potential aliases between access types are heavily restricted. It
is still possible to implement and verify pointer-based data structures in
|SPARK|, provided they do not involve cycles nor sharing. Typically, linked
lists or trees are supported, but not doubly linked lists or DAGs. Similarly,
iteration over linked structures is possible but restricted, as it involves
aliases. :ref:`Borrowing` can be used to traverse a list or search for a value
in an ordered tree, but more complex traversals, in particular those involving
a stack, are not possible, as borrowers cannot be stored inside data-structures.
Using explicit pointers and ownership is still the easiest way to implement
data-structures in |SPARK|, and should be preferred when it is possible. The
data-structure or the algorithms used to traverse it can sometimes be adapted.
As an example, it is possible to remove cycles in an implementation of
red-black-trees by removing the pointer to the parent and using a recursive
subprogram to rebalance the tree.

As an alternative to the above, it is possible to replace pointers by indexes
in an array. This can be done using an array per object, which requires making
the structure bounded, or using a big global array. The second has the
disadvantage of making it so all subprograms handling data-structures use the
same memory array, resulting in contracts and proof activities being needed to
check that modifying an object preserves the others. A somewhat similar result
can be achieved using the ``SPARK.Pointers`` library which models pointers as
a key in an abstract map of objects. The
``SPARK.Pointers.Pointers_With_Aliasing`` package uses a single memory object
per designated type, whereas the
``SPARK.Pointers.Pointers_With_Aliasing_Separate_Memory`` package allows
splitting memory into separate maps. In all cases, handling the structure of
the object usually requires complex invariants and reasoning, so it can be
heavy. The ``Simple_Allocator`` package below gives
an example of how a custom allocator can be implemented using indexes inside an
array. It uses a global array for the memory, but something similar can be
done by introducing a memory type and adding the memory object as a parameter
to ``Allocate`` and ``Free``:

.. literalinclude:: /examples/ug__simple_allocators/simple_allocator.ads
   :language: ada

.. literalinclude:: /examples/ug__simple_allocators/simple_allocator.adb
   :language: ada

Finally, it is possible for a user to implement their data-structures using the
whole expressivity of full Ada and hide it from |SPARK| analysis through pragma
or aspect ``SPARK_Mode``, see :ref:`Identifying SPARK Code`. However, since part
of the code is hidden from analysis, care should be taken to avoid breaking the
assumption made by the tool on the rest of the program (see
:ref:`Managing Assumptions`), in particular with respect to the
:ref:`Memory Ownership Policy` and more generally
:ref:`Absence of Interferences`. In particular, if the underlying data structure
uses pointers, it might be necessary to prevent the introduction of aliases
through copies either by making the type limited of by using an
:ref:`Annotation for Enforcing Ownership Checking on a Private Type`, unless
memory management is taken care off internally - through controlled types for
example.
