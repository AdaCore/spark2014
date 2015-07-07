.. _Usage Scenarios for SPARK:

***************************
Usage Scenarios for |SPARK|
***************************

This section discusses some of the common usage scenarios (or use cases) in
which |SPARK| may be used. It is illustrative, and is certainly not intended
to be an exhaustive list.

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
section 8.3.1.6 "Floating Point Operations" of the GNAT User's Guide.

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
of code that are in |SPARK|. For example, all execution paths in a |SPARK|
function should end with a return statement, a raise statement, or a ``pragma
Assert(False)``.

|GNATprove| reduces portability issues related to the use of fixed-point and
floating-point values:

* |GNATprove| supports a subset of fixed-point types and operations that
  ensures that the result of an operation always beloogs to the *perfect result
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
  be interpreted as ``(A + B) + C`` by a compiler, and ``A + (B + C)`` (after
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
  possible explicit raise of exceptions in the program.

The analysis of |GNATprove| can take into account characteristics of the target
by specifying a :ref:`Target Parameterization`.

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
Manual. By using the following restrictions (or a subset thereof), one can
ensure that the corresponding non-portable features are not used in the program:

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

* all possible run-time errors corresponding to raising exception
  ``Program_Error`` at run time

* all possible run-time errors corresponding to raising exception
  ``Constraint_Error`` at run time

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
fobidden in |SPARK|, the only possible cause for raising exception
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
can be modelled as mathematical functions of their inputs that always return
the same result when taking the same values in arguments. GNAT compiler was
modified to ensure this property (see
http://www.spark-2014.org/entries/detail/how-our-compiler-learnt-from-our-analyzers),
which may not hold for other Ada compilers.
