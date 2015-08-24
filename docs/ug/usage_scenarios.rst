.. _Usage Scenarios for SPARK:

***************************
Usage Scenarios for |SPARK|
***************************

This section discusses some of the common usage scenarios (or use cases) in
which |SPARK| may be used. It is illustrative, and is certainly not intended
to be an exhaustive list.

.. _Safe Coding Standard for Critical Software:

Safe Coding Standard for Critical Software
==========================================

|SPARK| is a subset of Ada meant for formal verification, by excluding features
that are difficult or impossible to analyze automatically. This means that
|SPARK| can also be used as a coding standard to restrict the set of features
used in critical software. As a safe coding standard checker, |SPARK| allows
both to prevent the introduction of errors by excluding unsafe Ada features,
and it facilitates their early detection with |GNATprove|'s flow analysis.

Exclusion of Unsafe Ada Features
--------------------------------

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

* Handling of exceptions is not permitted. Exception handling can create
  complex and invisible control flows in a program, which increase the
  likelihood of introducing errors during maintenance. What is more, when an
  exception is raised, subprograms that are terminated abnormally leave their
  variables in a possibly uninitialized or inconsistent state, in which data
  invariants may be broken. This includes values of out parameters, which
  additionnally are not copied back when passed by copy, thus introducing a
  dependency on the parameter mode chosen by the compiler.

* The use of access types and allocators is not permitted. Pointers can
  introduce aliasing, that is, they can allow the same object to be visible
  through different names at the same program point. This makes it difficult to
  reason about a program as modifying the object under one of the names will
  also modify the other names.  What is more, access types come with their on
  load of common mistakes, like double frees and dangling pointers.

* |SPARK| also prevents dependencies on the elaboration order by ensuring that
  no package can write into variables declared in other packages during its
  elaboration. The use of controlled types is also forbidden as they lead to
  insertions of implicit calls by the compiler. Finally, goto statements are
  not permitted as they obfuscate the control flow.

Early Detection of Errors
-------------------------

|GNATprove|'s flow analysis will find all the occurrences of the following
errors:

* uses of uninitialized variables (see :ref:`Data Initialization Policy`)

* aliasing of parameters that can cause interferences, which are often not
  accounted for by programmers (see :ref:`Absence of Interference`)

It will also warn systematically about the following suspicious behaviors:

* wrong parameter modes (can hurt readability and maintainability or even be
  the sign of a bug, for example if the programmer forgot to update a
  parameter, to read the value of an out parameter, or to use the initial value
  of a parameter)

* unused variables or statements (again, can hurt readability and
  maintainability or even be the sign of a bug)

.. _Address Data and Control Coupling:

Address Data and Control Coupling
=================================

As defined in the avionics standard DO-178, data coupling is `"The dependence
of a software component on data not exclusively under the control of that
software component"` and control coupling is `"The manner or degree by which
one software component influences the execution of another software
component"`, where a software component could be a subprogram, a unit or a set
of units.

Although analysis of data and control coupling are not performed at the same
level of details in non-critical domains, knowledge of data and control
coupling is important to assess impact of code changes. |SPARK| is ideally
equiped to support such analysis, with its detailed :ref:`Subprogram
Contracts`:

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

.. _Prove Absence of Run-Time Errors (AoRTE):

Prove Absence of Run-Time Errors (AoRTE)
========================================

With Proof Only
---------------

|GNATprove| can be used to prove the complete absence of possible run-time
errors corresponding to:

* raising exception ``Constraint_Error`` at run time,

* all possible failures of assertions corresponding to raising exception
  ``Assert_Error`` at run time, and

* all possible explicit raising of exceptions in the program.

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

|GNATprove| supports this type of combination of results in :ref:`The Analysis
Results Summary Table`. Multiple columns display the number of checks
automatically verified, while the column `Justified` displays the number of
checks manually justified. The column `Unproved` should be empty for all checks
to be verified.

With a Combination of Proof and Test
------------------------------------

It is not always possible to achieve 100% proof of AoRTE, for multiple reasons:

#. Formal verification is only applicable to the part of the program that is in
   |SPARK|. If the program includes parts in Ada that are not in |SPARK|, for
   example, then it is not possible to prove AoRTE on those parts.

#. Some run-time checks may not be proved automatically due to prover
   shortcomings (see :ref:`Investigating Prover Shortcomings` for details).

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

One way to get confidence that unproved run-time checks cannot fail during
execution is to exercize them during testing. Test coverage information allows
to guarantee a set of run-time checks have been executed successfully during a
test run. This coverage information may be gathered from the execution of a
unit testing campaign, an integration testing campaign, or the execution of a
dedicated testsuite focussing on exercizing the run-time checks (for example on
boundary values or random ones).

This strategy is already applied in other static analysis tools, for example in
the integration between the CodePeer static analyzer and the VectorCAST testing
tool for Ada programs.

Between Proof and Unit Testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Contracts on subprograms provide a natural boundary for combining proof and
test:

* If proof is used to demonstrate that a subprogram is free of run-time errors
  and respects its contract, this proof depends on the precondition of the
  subprogram being respected at the call site. This verification can be
  achieved by proving the caller too, or by checking dynamically the
  precondition of the called subprogram during unit testing for the caller.

* If proof is used to demonstrate that a subprogram is free of run-time errors
  and respects its contract, and this subprogram calls other subprograms, this
  proof depends on the postconditions of the called subprogram being respected
  at call sites. This verification can be achieved by proving the callees too,
  or by checking dynamically the postcondition of the called subprograms during
  their unit testing.

Thus, it is possible to combine freely subprograms that are proved and
subprograms that are unit tested, provided subprogram contracts
(:ref:`Preconditions` and :ref:`Postconditions`) are exercized during unit
testing. This can be achieved by compiling the program with assertions for
testing (for example with switch ``-gnata`` in |GNAT Pro|), or by using
GNATtest to create the test harness (see section 7.10.12 of |GNAT Pro| User's
Guide on `Testing with Contracts`).

This strategy is particularly well suited in the context of the DO-178C
certification standard in avionics, which explicitly allows proof or test to be
used as verification means on each module.

Between Proof and Integration Testing
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Contracts can also be exercized dynamically during integration testing. In
cases where unit testing is not required (either because proof has been applied
to all subprograms, or because the verification context allows it), exercizing
contracts during integration testing can complement proof results, by giving
the assurance that the actual compiled program behaves as expected.

This strategy has been applied at Altran on UK military projects submitted to
Def Stan 00-56 certification: AoRTE was proved on all the code, and contracts
were exercized during integration testing, which allowed to scrap unit testing.

.. _Prove Correct Integration Between Components:

Prove Correct Integration Between Components
============================================

|GNATprove| can be used to prove correct integration between components, where
a component could be a subprogram, a unit or a set of units. Indeed, even if
components are verified individually (for example by proof or test or a
combination thereof), their combination may still fail because of unforeseen
interactions or design problems.

|SPARK| is ideally is ideally equiped to support such analysis, with its
detailed :ref:`Subprogram Contracts`:

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

.. _Prove Functional Correctness:

Prove Functional Correctness
============================

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

.. _Safe Optimization of Run-Time Checks:

Safe Optimization of Run-Time Checks
====================================

Enabling run-time checks in a program usually increase the running time by
around 10%. This may not fit the timing schedule in some highly constrained
applications. In some cases where a piece of code is called a large number of
times (for example in a loop), enabling run-time checks on that piece of code
may increase the running time by far more than 10%. Thus, it may be tempting to
remove run-time checking in the complete program (with compilation switch
``-gnatp``) or a selected piece of code (with pragma ``Suppress``), for the
purpose of decreasing running time. The poblem with that approach is that the
program is not protected anymore against programming mistakes (for safety) or
attackers (for security).

|GNATprove| provides a better solution, by allowing users to prove the absence
of all run-time errors (or run-time errors of a specific kind, for example
overflow checks) in a piece of code, provided the precondition of the enclosing
subprogram is respected. Then, all run-time checks (or run-time errors of a
specific kind) can be suppressed in that piece of code using pragma
``Suppress``, knowing that they will never fail at run time, provided the
precondition of the enclosing subprogram is checked (for example by using
:ref:`Pragma Assertion_Policy`). By replacing many checks with one check, we
can decrease the running time of the application by doing safe and controlled
optimization of run-time checks.

.. _Ensure Portability of Programs:

Ensure Portability of Programs
==============================

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
target, or when changing compiler.  That's consistent with the definition of
portability in WikiPedia: "Portability in high-level computer programming is
the usability of the same software in different environments". As an example of
a difference between both interpretations, many algorithms which use
trigonometry are portable in the more common sense, not in the strictest sense.

Portability of Ada Programs
---------------------------

Programs with errors cause additional portability issues than programs without
errors, which is why we consider them separately.

Portability of Programs Without Errors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Ada Reference Manual defines precisely which features of the language
depend on choices by the compiler (see Ada RM 1.1.3 "Conformity of an
Implementation with the Standard"):

* *Implementation defined behavior* - The set of possible behaviors is
  specified in the language, and the particular behavior chosen in a compiler
  should be documented. An example of implementation defined behavior is the
  size of predefined integer types (like ``Integer``). All implementation
  defined behaviors are listed in Ada RM M.2, and GNAT documents its
  implementation for each of these points in section 7 "Implementation Defined
  Characteristics" of the GNAT Reference Manual.

* *Unspecified behavior* - The set of possible behaviors is specified in the
  language, but the particular behavior chosen in a compiler needs not be
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

* For some combinations of types of operands and results for fixed-point
  multiplication and division, the value of the result belongs to an
  implementation defined set of values (Ada RM G.2.3(5)).

* The semantics of operations on floating-point types is implementation defined
  (Ada RM G.2). It may or not follow the IEEE 754 floating point standard.

* The precision of elementary functions (exponential and trigonometric
  functions) is implementation defined (Ada RM G.2.4).

Section 18.1 "Writing Portable Fixed-Point Declarations" of the GNAT Reference
Manual gives some advice on how to reduce implementation defined behavior for
fixed-point types. Use of IEEE 754 floating-point arithmetic can be enforced in
GNAT by using the compilation switches "-msse2 -mfpmath=sse", as documented in
section 8.3.1.6 "Floating Point Operations" of the |GNAT Pro| User's Guide.

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
   be exercized to use these constructs with other compilers, or older versions
   of |GNAT Pro|. This issue is detailed in section :ref:`Portability Issues`.

.. _Portability of Programs With Errors:

Portability of Programs With Errors
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In addition to the portability issues discussed so far, programs with errors
cause specific portability issues related to whether errors are detected and
how they are reported. The Ada Reference Manual distinguishes between four
types of errors (see Ada RM 1.1.5 "Classification of Errors"):

* *Compile-time errors* - These errors make a program illegal, and should be
  detected by any Ada compiler. They do not cause any portability issue, as
  they must be fixed before compilation.

* *Run-time errors* - These errors are signaled by raising an exception at run
  time. They might be a cause of portability problems, as a change of compiler
  and/or target may lead to new run-time errors. For example, a new compiler
  may cause the program to use more stack space, leading to an exception
  ``Storage_Error``, and a new target may change the size of standard integer
  types, leading to an exception ``Constraint_Error``.

* *Bounded errors* - These errors need not be detected either at compiler time
  or at run time, but their effects should be bounded. For example, reading an
  uninitialized value may result in any value of the type to be used, or to
  ``Program_Error`` being raised. Like for run-time errors, they might be a
  cause of portability problems, as a change of compiler and/or target may lead
  to new bounded errors.

* *Erroneous execution* - For the remaining errors, a program exhibits
  erroneous execution, which means that the error needs not be detected, and
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

.. _Benefits of Using SPARK for Portability:

Benefits of Using |SPARK| for Portability
-----------------------------------------

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
  portability. See :ref:`Tool Limitations`.

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
  re-ordering) by another compiler. Note that GNAT always use the former
  version without re-ordering. See :ref:`Parenthesized Arithmetic Operations`.

* In modes ``flow``, ``prove`` and ``all``, |GNATprove| issues high check
  messages on possible parameter aliasing, when such an aliasing may lead to
  interferences. This includes all cases where the choice of parameter passing
  mechanism in a compiler (by copy or by reference) might influence the
  behavior of the subprogram. See :ref:`Absence of Interference`.

* In modes ``flow``, ``prove`` and ``all``, |GNATprove| issues check messages
  on possible reads of uninitialized data. These messages should be reviewed
  with respect to the stricter :ref:`Data Initialization Policy` in |SPARK|
  than in Ada. Hence, it is possible when the program does not conform to the
  stricter |SPARK| rules to manually validate them, see section
  :ref:`Justifying Check Messages`.

* In modes ``prove`` and ``all``, |GNATprove| issues check messages on all
  possible run-time errors corresponding to raising exception
  ``Constraint_Error`` at run time, all possible failures of assertions
  corresponding to raising exception ``Assert_Error`` at run time, and all
  possible explicit raising of exceptions in the program.

The analysis of |GNATprove| can take into account characteristics of the target
(size and alignment of standard scalar types, endianness) by specifying a
:ref:`Target Parameterization`.

How to Use |SPARK| for Portability
----------------------------------

|GNATprove|'s analysis may be used to enhance the portability of programs. Note
that the guarantees provided by this analysis only hold for the source
program. To ensure that these guarantees extend to the executable object code,
one should independently provide assurance that the object code correctly
implements the semantics of the source code.

Avoiding Non-Portable Features
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
  bounds. For example, a user-defined type ranging from 1 to 100 will be given
  a base type ranging from -128 to 127 by both |GNAT Pro| and |GNATprove|. The
  choice of base types influences in which cases intermediate overflows may be
  raised during computation. The choice made in |GNATprove| is the strictest
  one among existing compilers, as far as we know, which ensures that
  |GNATprove|'s analysis detects a superset of the overflows that may occur at
  run time.

* Issues related to errors. See section :ref:`Avoiding Errors to Enhance
  Portability`.

* Issues related to the use of fixed-point or floating-point operations. See
  section :ref:`Portability of Fixed-Point and Floating-Point Computations`
  below.

.. _Avoiding Errors to Enhance Portability:

Avoiding Errors to Enhance Portability
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Because errors in a program make portability particularly challenging (see
:ref:`Portability of Programs With Errors`), it is important to ensure that a
program is error-free for portability. |GNATprove|'s analysis can help by
ensuring that the |SPARK| parts of a program are free from broad kinds of
errors:

* all possible reads of uninitialized data

* all possible run-time errors except raising exception ``Storage_Error``,
  corresponding to raising exception ``Program_Error``, ``Constraint_Error`` or
  ``Tasking_Error`` at run time

* all possible failures of assertions corresponding to raising exception
  ``Assert_Error`` at run time

* all possible explicit raise of exceptions in the program

When parts of the program are not in |SPARK| (for example, in Ada or C), the
results of |GNATprove|'s analysis depend on assumptions on the correct behavior
of the non-|SPARK| code. For example, callers of a |SPARK| subprogram should
only pass initialized input values, and non-|SPARK| subprograms called from
|SPARK| code should respect their postcondition. See section :ref:`Managing
Assumptions` for the complete list of assumptions.

In particular, when changing the target characteristics, |GNATprove|'s analysis
can be used to show that no possible overflow can occur as a result of changing
the size of standard integer types.

|GNATprove|'s analysis does not detect possible run-time errors corresponding
to raising exception ``Storage_Error`` at run time, which should be
independently assessed. Because access types and dynamic allocation are
forbidden in |SPARK|, the only possible cause for raising exception
``Storage_Error`` in a |SPARK| program is overflowing the stack.

.. _Portability of Fixed-Point and Floating-Point Computations:

Portability of Fixed-Point and Floating-Point Computations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
modified to ensure this property (see
http://www.spark-2014.org/entries/detail/how-our-compiler-learnt-from-our-analyzers),
which may not hold for other Ada compilers.

.. _develop new code from scratch:

Develop New Code from Scratch
=============================

This is the 'green field' development scenario where new software is
being written and there are no constraints imposed in terms of having
to base the development on pre-existing code. |SPARK| may be used for
all software components or (more likely) the software may be developed
in a mixture of |SPARK|, full Ada and other languages. For example, Ada
may be employed in modules where it is deemed essential to make use of
language features that are not currently in the |SPARK| subset, or in
a safety-related project |SPARK| might be used for all of the
safety-related software components.

A typical development process for this scenario might be:

#. Produce the high level (architectural) design in terms of package
   specifications. Determine which packages will be in |SPARK| and add
   contracts to those packages. The package contracts identify the
   key elements of abstract state, and the subprogram global contracts
   show which subprograms read and write that state. Optionally, dependency
   contracts can be added to specify information flow relations, and
   postconditions can be added to specify high-level properties such
   as safety requirements that must be satisfied.

#. Identify the |SPARK| packages with the ``SPARK_Mode`` aspect. At this
   stage the high-level package structure can be analyzed with the tools (using
   the 'Examine' command in GPS/GNATbench) before any executable code is
   implemented.

#. Alternatively, if the majority of packages are to be |SPARK|, then a
   project should use ``SPARK_Mode`` as a configuration pragma, and only
   apply ``SPARK_Mode => Off`` selectively for those few units that are
   not |SPARK|.

#. Begin implementing the package bodies. One typical method of doing this
   is to use a process of top-down decomposition, starting with a top-level
   subprogram specification and implementing the body by breaking it down
   into further (nested) subprograms which are themselves specified but not
   yet implemented, and to iterate until a level is reached where it is
   appropriate to start writing executable code. However the exact process
   is not mandated and will depend on other factors such as the design
   methodology being employed.

#. As each subprogram is implemented it can be verified (against its contract,
   and to show absence of run-time errors) by proof, testing (with assertion
   checking enabled) or both.

   - Users may opt to try proving first then, if a particular proof is
     tricky to discharge, execute test cases to either give confidence that
     the code and contract is correct or to help diagnose why it is failing.

   - Alternatively, users may prefer to execute the code with suitable
     test cases during development, then use proof to verify it once they
     believe it to be correct.

#. Once verification is complete the executable can be compiled with
   assertion checks either enabled or disabled depending on the policy chosen
   by the project.

.. _convert SPARK 2005 to SPARK 2014:

Convert existing SPARK 2005 software to SPARK 2014
==================================================

If an existing piece of software has been developed in SPARK 2005 and is
still undergoing active development/maintenance then it may be advantageous
to upgrade to using SPARK 2014 in order to make use of the larger language
subset and the new tools and environment. The |SPARK| Language Reference Manual
has an appendix containing a SPARK 2005 to |SPARK| Mapping Specification which
can be used to guide the conversion process. As the |SPARK| subset is larger
than the SPARK 2005 subset, and the mapping of features between the two languages
is defined, the translation should be relatively straightforward. There are two
main options for the conversion process:

#. All of the software is converted from SPARK 2005 to |SPARK| at the same time.
   The |SPARK| tools should be used to analyze the work in progress throughout
   the conversion process (which implies that a bottom-up approach may work best)
   and any errors corrected as they are found. Once the conversion is complete,
   development and maintenance can continue in |SPARK|.

#. A more gradual approach could be employed, where code is only converted to
   |SPARK| when it needs to be changed. (The granularity of how much code needs
   to be converted when a module is touched should be considered, and is likely to
   be at the level of the whole package.) The |SPARK| tools can then be used to
   analyze the new/changed code, and will attempt to analyze any dependent units,
   which may or may not be in |SPARK|. It is not necessary for dependent units to
   be fully in |SPARK| but any declarations from them that are used in |SPARK|
   packages must be in |SPARK|. Note that the latest version of the SPARK 2005
   toolset facilitates this migration by ignoring |SPARK| pragmas.

Note that some users may wish to take advantage of the new |SPARK| contracts
and tools whilst retaining the more restrictive nature of SPARK 2005. (Many
of the restrictions from SPARK 2005 have been lifted in |SPARK| because
improvements in the tools mean that sound analysis can be performed without
them, but some projects may need to operate in a more constrained environment.)
This can be achieved using ``pragma Restrictions (SPARK_05)``. For further details
of this restriction please see the GNAT Reference Manual.

.. _analyze legacy Ada software:

Analyze Legacy Ada Software
===========================

If a legacy system has been developed in Ada then analyzing it with the |SPARK|
tools may be a good first step in order to assess the quality of the code prior
to performing a full or partial conversion to |SPARK|. The suggested workflow is:

#. Identify units which are highest priority for conversion to |SPARK|. These may
   already be known, or potential candidates could be identified by:

   - putting pragma SPARK_Mode in a global configuration file so that all code is
     analyzed as if it were intended to be |SPARK|;

   - running the 'Examine' command on all code;

   - use the errors in the summary report to guide the selection process - files
     with fewer errors are likely to be easier to convert and would be a good
     starting point;

   - remove the global configuration pragma SPARK_Mode before proceeding.

#. For each unit to be converted to |SPARK|:

   - Identify the specification as |SPARK| (SPARK_Mode => On) but identify the body
     as not in |SPARK| (SPARK_Mode => Off).

   - Analyze (Examine) the specification and correct any errors that are reported
     by the tools, iterating until no errors remain.

   - Mark the body as |SPARK| (change SPARK_Mode from Off to On).

   - Analyze (Examine) the body and correct any errors that are reported
     by the tools, iterating until no errors remain.

   - Each subprogram can then be verified to show absence of run-time errors by proof,
     testing (with assertion checking enabled) or both.

     - Users may opt to try proving first then, if a particular proof is
       tricky to discharge, execute test cases to either give confidence that
       the code is correct or to help diagnose why it is failing.

     - Alternatively, users may prefer to execute the code with suitable
       test cases first, then use proof to verify it once they believe it
       to be correct.

#. Once conversion and verification is complete, the executable can be compiled with
   assertion checks either enabled or disabled depending on the policy chosen
   by the project. At this point users might begin adding contracts to the code in
   order to perform verification of functional properties.
