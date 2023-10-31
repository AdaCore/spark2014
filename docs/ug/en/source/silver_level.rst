The goal of this level is to ensure that the program does not raise an
unexpected
exception at run time. Among other things, this guarantees that the control
flow of the program cannot be circumvented by exploiting a buffer overflow,
or integer overflow. This also ensures that
the program cannot crash or behave erratically when compiled without
support for run-time checking (compiler switch ``-gnatp``) because of
operations that would have triggered a run-time exception.

.. index:: Constraint_Error
.. index:: Assertion_Error

GNATprove can be used to prove the complete absence of possible run-time
errors corresponding to the explicit raising of unexpected exceptions in the
program, raising the exception ``Constraint_Error`` at run time, and
failures of assertions (corresponding to raising exception ``Assertion_Error``
at run time).

.. index:: Precondition
.. index:: Defensive code

A special kind of run-time error that can be proved at this level is the
absence of exceptions from defensive code. This requires users to add
subprogram preconditions (see section :ref:`Preconditions` for details) that
correspond to the conditions checked in defensive code. For example, defensive
code that checks the range of inputs is modeled by a precondition of the
form ``Input_X in Low_Bound .. High_Bound``. These conditions are then checked by
GNATprove at each call.

.. rubric:: Benefits

The SPARK code is guaranteed to be free from run-time errors (Absence of Run
Time Errors - AoRTE) plus all the defects already detected at Bronze level: no
reads of uninitialized variables, no possible interference between parameters
and/or global variables, no unintended access to global variables, and no
infinite loop or recursion in functions. These guarantees extend to code using
features that require proof for ensuring correct initialization and
termination, as described in the limitations for :ref:`Bronze Level <Bronze
Level>`.  Thus, the quality of the program can be guaranteed to achieve higher
levels of integrity than would be possible in other programming languages.

All the messages about possible run-time errors can be carefully reviewed
and justified (for example by relying on external system constraints such
as the maximum time between resets) and these justifications can be later
reviewed as part of quality inspections.

.. index:: -gnatp switch (compiler)
.. index:: C language

The proof of AoRTE can be used to compile the final executable without
run-time exceptions (compiler switch ``-gnatp``), which results in very
efficient code comparable to what can be achieved in C or assembly.

.. index:: DO-178C / ED-12C
.. index:: EN 50128
.. index:: CENELEC EN 50128
.. index:: IEC 61508
.. index:: ECSS-Q-ST-80C
.. index:: IEC 60880
.. index:: IEC 62304
.. index:: ISO 26262
.. index:: Qualification (for GNATprove)

The proof of AoRTE can be used to comply with the objectives of
certification standards in various domains (DO-178B/C in avionics, EN 50128 in
railway, IEC 61508 in many safety-related industries, ECSS-Q-ST-80C in
space, IEC 60880 in nuclear, IEC 62304 in medical, ISO 26262 in
automotive). To date, the use of SPARK has been qualified in an EN 50128
context. Qualification plans for DO-178 have been developed by AdaCore.
Qualification material in any context can be developed by AdaCore as
part of a contract.

.. rubric:: Impact on Process

.. index:: Precondition
.. index:: Postcondition
.. index:: False alarm

An initial pass is required where proof of AoRTE is applied to the program,
and the resulting messages are resolved by either rewriting code or
justifying any false alarms. Once this is complete, as for the Bronze
level, ongoing maintenance can retain the same guarantees at reasonable
cost. Using precise types and simple subprogram contracts (preconditions
and postconditions) is sufficient to avoid most false alarms, and any
remaining false alarms can be easily justified.

.. index:: Loop_Invariant; for Silver level

Special treatment is required for loops, which may need the addition of loop
invariants to prove AoRTE inside and after the loop. See the relevant sections
of the SPARK User's Guide for a description of the detailed process for adding
loop contracts, as well as examples of common patterns of loops and their
corresponding loop invariants.

.. rubric:: Costs and Limitations

The guarantees offered at Silver level and above do not extend to subprograms
with the annotations ``Skip_Flow_And_Proof`` or ``Skip_Proof``, which are only
analyzed at Stone or Bronze level respectively.

The initial pass may require a substantial effort to resolve all false
alarms, depending on the coding style adopted previously. The analysis may
take a long time, up to a few hours, on large programs but is guaranteed to
terminate. Proof is, by construction, limited to local understanding of the
code, which requires using sufficiently precise types of variables, and
some preconditions and postconditions on subprograms to communicate
relevant properties to their callers.

Even if a property is provable, automatic provers may nevertheless not be
able to prove it, due to limitations of the heuristic techniques used in
automatic provers. In practice, these limitations mostly show up on
non-linear integer arithmetic (such as division and modulo) and
floating-point arithmetic.
