Introduction
============

|SPARK| is a programming language and a set of verification tools
designed to meet the needs of high-assurance software development.
|SPARK| is based on Ada 2012, both subsetting the language to remove
features that defy verification and also extending the system of
contracts by defining new Ada aspects to support modular, formal verification.

The new aspects support abstraction and refinement and facilitate deep static
analysis to be performed including information-flow analysis and formal
verification of an implementation against a specification.

|SPARK| is a much larger and more flexible language than its
predecessor SPARK 2005. The language can be configured to suit
a number of application domains and standards, from server-class
high-assurance systems to embedded, hard real-time, critical systems.

A major feature of |SPARK| is the support for a mixture of proof and
other verification methods such as testing, which
facilitates the use of unit proof in place of unit testing; an approach now
formalized in DO-178C and the DO-333 formal methods supplement.
Certain units may be formally proven and other units validated through
testing.

The new aspects defined for |SPARK| all have equivalent pragmas which allows a
|SPARK| program to be compiled by and executed by any Ada implementation; for
instance an Ada 95 compiler provided the use of Ada 2005 and Ada 2012 specific
features are avoided.  The |SPARK| attributes Update and Loop_Entry can be used
only if the Ada implementation supports them.  Additionally the attribute Old
can be used in only a postcondition and not in a pragma.

The direct use of the new aspects requires an Ada 2012 compiler which supports them
in a way consistent with the definition given here in the |SPARK| reference manual.
The GNAT implementation is one such compiler.

Structure of Introduction
-------------------------

This introduction contains the following sections:

- Section :ref:`lifecycle` describes how this document will evolve up to
  and beyond the first formal release of the |SPARK| language and toolset.

- Section :ref:`read_interpret` describes how to read and interpret this document.

- Section :ref:`desc_notate` describes the conventions used in presenting
  the definition of |SPARK|.

- Section :ref:`formal_analysis` gives a brief overview of the formal analysis
  to which |SPARK| programs are amenable.

- Section :ref:`dynamic_sem` gives details on the dynamic semantics of
  |SPARK|.

- Section :ref:`sprs` defines the overall goals to be met by the |SPARK| language and
  toolset.

- Section :ref:`explain_sprs` provides expanded detail on the main strategic requirements.

- Section :ref:`notes` provides some brief detail on the current status and contents
  of this document.


.. _lifecycle:

Lifecycle of this Document
--------------------------

This document will be developed incrementally towards a number of milestones
-- this version of the document represents Milestone 3 --
culminating in Release 1 of the document that matches the first formal release
of the toolset. Subsequent releases of the document will follow, associated with
subsequent formal releases of the toolset. Hence, where inclusion of particular
scope is deferred, it may be deferred to:

- A specified milestone, meaning that the feature will be included in the first
  formal release of the toolset.

- A release subsequent to Release 1, meaning that the feature will be
  implemented *after* the first formal release of the toolset.

Note that the content currently in scope for the current draft of this document will only
be regarded as definitive when the Release 1 version of the document is ready,
and so may be subject to change.

.. _read_interpret:

How to Read and Interpret this Manual
-------------------------------------

This RM (reference manual) is *not* a tutorial guide
to |SPARK|.  It is intended as a reference guide for
users and implementors of the language.  In this context,
"implementors" includes those producing both compilers and
verification tools.

This manual is written in the style and language of the Ada 2012 RM,
so knowledge of Ada 2012 is assumed.  Chapters 2 through 13 mirror
the structure of the Ada 2012 RM.  Chapter 14 covers all the annexes
of the Ada 2012 RM. Moreover, this manual should be interpreted as an extension
of the Ada 2012 RM (that is, |SPARK| is fully defined by this document taken together
with the Ada 2012 RM).

|SPARK| introduces a number of aspects. The language rules are written as if all
the |SPARK| specific aspects are present but minimum requirements are placed on
a tool which analyzes |SPARK| to be able to synthesize (from the source code)
some of these aspects if they are not present. A tool may synthesize more
aspects than the minimum required (see :ref:`verific_modes`). An equivalent
pragma is available for each of the new aspects but these are not covered
explicitly in the language rules either.

Readers interested in how SPARK 2005 constructs and idioms map into
|SPARK| should consult the appendix :ref:`mapping-spec-label`.

.. _desc_notate:

Method of Description
---------------------

In expressing the aspects, pragmas, attributes and rules of |SPARK|,
the following chapters of this document follow the notational conventions of
the Ada 2012 RM (section 1.1.4).

The following sections are given for each new language feature introduced
for |SPARK|, following the Ada 2012 RM (other than *Verification Rules*,
which is specific to |SPARK|):

#. Syntax: this section gives the format of any |SPARK| specific syntax.

#. Legality Rules: these are rules that are enforced at compile time. A
   construct is legal if it obeys *all* of the Legality Rules.

#. Static Semantics: a definition of the compile-time effect of each construct.

#. Dynamic Semantics: a definition of the run-time effect of each construct.

#. Verification Rules: these rules define checks to be performed on the language
   feature that relate to static analysis rather than simple legality rules.

#. Name Resolution Rules: There are very few |SPARK| specific name resolution
   rules.  Where they exist they are placed under this heading.

A section might not be present if there are no rules specific to |SPARK|
associated with the language feature.

When presenting rules, additional text may be provided in square brackets [ ].
This text is redundant in terms of defining the rules themselves and simply provides
explanatory detail.

In addition, examples of the use of the new features are given along with the
language definition detail.

.. todo::
     We need to increase the number of examples given. To be completed in the Milestone 4
     version of this document.

.. _formal_analysis:

Formal Analysis
---------------

|SPARK| will be amenable to a range of formal analyses, including but not
limited to the following static analysis techniques:

- Data-flow analysis, which considers the initialization of variables and the
  data dependencies of subprograms (which parameters and variables get read or
  written).

- Information-flow analysis, which also considers the coupling between the
  inputs and outputs of a subprogram (which input values of parameters and
  variables influence which output values). The term *flow analysis* is used to
  mean data-flow analysis and information-flow analysis taken together.

- Formal verification of robustness properties. In Ada terminology, this refers to
  the proof that certain predefined checks, such as the ones which could raise
  Constraint_Error, will never fail at run time and hence the corresponding exceptions
  will not be raised.

- Formal verification of functional properties, based on contracts expressed as
  preconditions, postconditions, type invariants and so on. The term *formal verification*
  is used to mean formal verification of robustness properties and formal verification of
  functional properties taken together.

Data and information-flow analysis is not valid and might not be possible if the
legality rules of Ada 2012 and those presented in this document are not met.
Similarly, a formal verification might not be possible if the legality rules are
not met and may be unsound if data-flow errors are present.


.. todo::
      Consider adding a glossary, defining terms such as flow analysis and formal verification.
      To be completed in the Milestone 4 version of this document.

Further Details on Formal Verification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Many Ada constructs have dynamic semantics which include a requirement
that some error condition must or may\ [#bounded_errors]_ be checked,
and some exception  must or may\ [#bounded_errors]_  be raised, if the error is
detected  (see Ada 2012 RM 1.1.5(5-8)).  For example, evaluating the name of an
array component includes a check that each index value belongs to the
corresponding index range of the array (see Ada 2012 RM 4.1.1(7)).

For every such run-time check a corresponding obligation to prove that the error
condition cannot be true is introduced. In particular, this rule applies to the
run-time checks associated with any assertion (see Ada 2012 RM (11.4.2));
the one exception to this rule is pragma
``Assume`` (see :ref:`pragma_assume`).

In addition, the generation of proof obligations is unaffected by the
suppression of checks (e.g., via pragma ``Suppress``) or the disabling of
assertions (e.g., via pragma ``Assertion_Policy``). In other words, suppressing
or disabling a check does not prevent generation of its associated proof
obligations.

All such generated proof obligations must be discharged before the
formal program verification phase may be considered to be complete.

.. [#bounded_errors] In the case of some bounded errors a check and any resulting
   exception only *may* be required.

Note that formal verification of a program must take acount
of the machine on which that program is executed and the properties of the tools
used to compile and build it. In such cases it must be possible to represent the dependencies as explicit
inputs to the formal verification process.


.. _dynamic_sem:

Dynamic Semantics of |SPARK| Programs
-------------------------------------

Every valid |SPARK| program is also a valid Ada 2012 program.
The |SPARK| dynamic semantics are the same as Ada 2012 with the
exception of some new aspects, pragmas and attributes which have
dynamic semantics. Additionally, the new dynamic semantics only
affect assertion expressions so if assertion expressions are
ignored then the dynamic semantics of an Ada 2012 program are
the same as a |SPARK| program.

|SPARK| programs that have failed their static analysis checks can still be
valid Ada 2012 programs. An incorrect |SPARK| program with, say, flow
analysis anomalies or undischarged proof obligations can still be executed as
long as the Ada compiler in question finds nothing objectionable. What one gives
up in this case is the formal analysis of the program, such as proof of absence
of run-time errors or the static checks performed by flow analysis such as the
proof that all variables are initialized before use.

|SPARK| may make use of certain aspects, attributes and pragmas which are not
defined in the Ada 2012 reference manual. Ada 2012 explicitly permits
implementations to provide implementation-defined aspects, attributes and
pragmas. If a |SPARK| program uses one of these aspects (e.g., Global), or
attributes (e.g., Update) then it can only be compiled and executed by an
implementation which supports the construct in a way consistent with the
definition given here in the |SPARK| reference manual.

If the equivalent pragmas are used instead of the implementation-defined aspects
and if the use of implementation-defined attributes is avoided, then a |SPARK|
program may be compiled and executed by any Ada implementation (whether or not
it recognizes the |SPARK| pragmas). Ada specifies that unrecognized pragmas are
ignored: an Ada compiler that ignores the pragma is correctly implementing the
dynamic semantics of |SPARK| and the |SPARK| tools will still be able to
undertake all their static checks and proofs.

.. todo::
      The pragmas equivalent to the new aspects need to be added to this document.
      To be added in the Milestone 4 version of this document.

Main Program
------------

In SPARK 2005, a dedicated annotation was used to identify the main program.
There is no corresponding aspect in |SPARK| and instead it is expected that
any implementation of |SPARK| will have its own mechanism to allow the tools
to identify the main program (albeit not within the language itself).

.. _sprs:

|SPARK| Strategic Requirements
------------------------------

The following requirements give the principal goals to be met by |SPARK|.
Some are expanded in subsequent sections within this chapter.

- The |SPARK| language subset shall embody the largest subset of Ada 2012 to
  which it is currently practical to apply automatic formal verification, in line with
  the goals below. However, future advances in verification research and
  computing power may allow for expansion of the language and the forms of
  verification available. See section :ref:`main_restricts`
  for further details.

- The use of Ada 2012 preconditions, postconditions and other assertions
  dictates that |SPARK| shall have executable semantics for assertion
  expressions. Such expressions may be executed, proven or both. To avoid having
  to consider potential numeric overflows when defining an assertion expression
  |SPARK| mandates a mode whereby extended or infinite integer arithmetic is
  supported for assertion expressions. The way in which this mode is selected is
  tool dependent and shall be described in the user guide for the tool. If this
  mode is not active, proof obligations to demonstrate the absence of overflow
  in assertion expressions will be present.

- |SPARK| shall provide for mixing of verification evidence generated by formal
  analysis [for code written in the |SPARK| subset] and evidence generated by
  testing or other traditional means [for code written outside of the core
  |SPARK| language, including legacy Ada code, or code written in the |SPARK|
  subset for which verification evidence could not be generated]. See section
  :ref:`test_and_proof` for further details. Note, however, that a core goal of
  is to provide a language expressive enough for the whole of a program
  to written in |SPARK| making it potentially entirely provable largely using
  automatic proof tools.

- |SPARK| shall support *constructive*, modular development which allows
  contracts to be specified on the declaration of program units and allows
  analysis and verification to be perfomed based on these contracts as early as
  possible in the development lifecycle, even before the units are
  implemented. As units are implemented the implementation is verified against
  its specification given in its contract. The contracts are specified using
  |SPARK| specific aspects.

- A |SPARK| analysis tool is required to synthesize at least some of the |SPARK|
  specific aspects, used to specify the contract of a program unit, if a
  contract is not explicitly specified, for instance the :ref:`global-aspects`
  and the :ref:`depends-aspects` from the implementation of the unit if it
  exists. The minimum requirements are given in :ref:`verific_modes` but a
  particular tool may provide more precise synthesis and the synthesis of more
  aspects. The synthesized aspect is used in the analysis of the unit if the
  aspect is not explicitly specified. The synthesis of |SPARK| specific aspects
  facilitates different development strategies and the analysis of pre-existing
  code (see section :ref:`verific_modes`).

- Although a goal of |SPARK| is to provide a language that supports as many
  Ada 2012 features as practical, there is another goal which is to support good
  programming practice guidelines and coding standards applicable to certain
  domains or standards. This goal is met by *Code Policies* that shall be
  allowed that reduce the subset of |SPARK| that may be used in line with
  specific goals such as domain needs or certification requirements. The use of
  a code policy may also have the effect of simplifying proof or analysis. See
  section :ref:`code_policy` for further details.

- |SPARK| shall allow the mixing of code written in the |SPARK| subset
  with code written in full Ada 2012. See section :ref:`in_out` for
  further details.

- Many systems are not written in a single programming language. |SPARK| shall
  support the development, analysis and verification of programs which are only
  partly in |SPARK|, with other parts in another language, for instance, C.
  |SPARK| specific aspects manually specified at unit level will form the
  boundary interface between the |SPARK| and other parts of the program. *No
  further detail is given in the current draft of this document on mixing SPARK
  2014 code with non-Ada code.*

  .. todo::
     Complete detail on mixing |SPARK| with non-Ada code.
     To be completed in the Milestone 4 version of this document.

- |SPARK| shall support entities which do not affect the functionality of
  a program but may be used in the test and verification of a program.
  See section :ref:`ghost_entities`.

- |SPARK| shall provide counterparts of all language features and analysis
  modes provided in SPARK 83/95/2005, unless it has been identified that customers
  do not find them useful.

- Enhanced support for specifying and verifying properties of secure systems
  shall be provided (over what is available in SPARK 2005). [The features to
  provide this enhanced support are not yet fully defined and will not be
  implemented until after release 1 of the |SPARK| tools.]

- |SPARK| shall support the analysis of external communication channels, which
  might be volatile variables, typically either an input or an output.
  See section :ref:`volatile` for further details.

- The language shall offer an unambiguous semantics. In Ada terminology, this
  means that all erroneous and unspecified behavior shall be eliminated either
  by direct exclusion or by adding rules which indirectly guarantee that some
  implementation-dependent choice, other than the fundamental data types and
  constants, cannot effect the externally-visible behavior of the program. For
  example, Ada does not specify the order in which actual parameters are
  evaluated as part of a subprogram call. As a result of the SPARK rules which
  prevent the evaluation of an expression from having side effects, two
  implementations might choose different parameter evaluation orders for a given
  call but this difference won't have any observable effect. [This means
  implementation-defined and partially-specified features may be outside of
  |SPARK| by definition, though their use could be allowed and a warning or
  error generated for the user. See section :ref:`in_out` for further details.]
  *Note that the current draft of this document does not necessarily define all
  restrictions necessary to guarantee an unambiguous semantics.*

- |SPARK| shall support provision of "formal analysis" as defined by DO-333,
  which states "an analysis method can only be regarded as formal analysis if
  its determination of a property is sound. Sound analysis means that the method
  never asserts a property to be true when it is not true." A language with
  unambiguous semantics is required to achieve this and additionally any other
  language feature that for which sound analysis is difficult or impractical
  will be eliminated or its use constrained to meet this goal. See section
  :ref:`main_restricts` for further details. *Note that the current draft of
  this document does not necessarily define all restrictions necessary to
  guarantee soundness.*

.. todo::
   Ensure that all strategic requirements have been implemented.
   To be completed in the Milestone 4 version of this document.

.. todo::
   Where Ada 2012 language features are designated as not in SPARK 2014 in subsequent
   chapters of this document, add tracing back to the strategic requirement that
   motivates that designation. To be completed in the Milestone 4 version of this document.

.. _explain_sprs:

Explaining the Strategic Requirements
----------------------------------------

The following sections provide expanded detail on the main strategic requirements.

.. _main_restricts:

Principal Language Restrictions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To facilitate formal analyses and verification, |SPARK| enforces a number of
global restrictions to Ada 2012. While these are covered in more detail
in the remaining chapters of this document, the most notable restrictions are:

- The use of access types and allocators is not permitted.

- All expressions (including function calls) are free of side-effects.

- Aliasing of names is not permitted in general but the renaming of entities is
  permitted as there is a static relation ship between the two names.  In
  analysis all names introduced by a renaming declaration are replaced by the
  name of the renamed entity. This replacement is applied recursively when there
  are multiple renames of an entity.

- The goto statement is not permitted.

- The use of controlled types is not currently permitted.

- Tasking is not currently permitted (it is intended that this will be included
  in Release 2 of the |SPARK| language and tools).

- Raising and handling of exceptions is not currently permitted (exceptions can
  be included in a program but proof must be used to show that they cannot be
  raised).


.. _test_and_proof:

Combining Formal Verification and Testing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are common reasons for combining formal verification on some part
of a codebase and testing on the rest of the codebase:

#. Formal verification is only applicable to a part of the codebase. For
   example, it might not be possible to apply the necessary formal verification to Ada code
   that is not in |SPARK|.

#. Formal verification only gives strong enough results on a part of the
   codebase. This might be because the desired properties cannot be expressed
   formally, or because proof of these desired properties cannot be
   sufficiently automated.

#. Formal verification might be only cost-effective on a part of the codebase. (And
   it may be more cost-effective than testing on this part of the codebase.)

Since the combination of formal verification and testing cannot guarantee the
same level of assurance as when formal verification alone is used, the goal
when combining formal verification and testing is to
reach a level of confidence at least as good as the level reached by testing alone.

Mixing of formal verification and testing requires consideration of at least the
following three issues.

Demarcating the Boundary between Formally Verified and Tested Code
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Contracts on subprograms provide a natural boundary for this combination. If a
subprogram is proved to respect its contract, it should be possible to call it
from a tested subprogram. Conversely, formal verification of a subprogram
(including absence of run-time errors and contract checking) depends on called
subprograms respecting their own contracts, whether these are verified by
formal verification or testing.

In cases where the code to be tested is not |SPARK|, then additional information
may be provided in the code -- possibly at the boundary -- to indicate this
(see section :ref:`in_out` for further details).


Checks to be Performed at the Boundary
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When a tested subprogram T calls a proved subprogram P, then the precondition
of P must hold. Assurance that this is true is generated by executing
the assertion that P's precondition holds during the testing of T.

Similarly, when a proved subprogram P calls a tested subprogram T, formal
verification will have shown that the precondition of T holds. Hence, testing
of T must show that the postcondition of T holds by executing the corresponding
assertion.  This is a necessary but not necessarily sufficient condition.
Dynamically, there is no check that the subprogram has not updated entities
not included in the postcondition.

In general, formal verification works by imposing requirements on the callers of
proved code, and these requirements should be shown to hold even when formal
verification and testing are combined. Any toolset that proposes a combination
of formal verification and testing for |SPARK| should provide a detailed process
for doing so, including any necessary additional testing of proof assumptions.

Restrictions that Apply to the Tested Code
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

There are two two sources of restriction that apply to the tested code:

#. The need to validate a partial proof that relies on code that is not
   itself proven but is only tested.

#. The need to validate the assumptions on which a proof is based when
   proven code is combined with tested code.

The specific details of the restrictions to be applied to tested code -- which
will typically be non-|SPARK| -- code will be given in a subsequent draft of this document.

*No further detail is given in the current draft of this document on Combining
Formal Verification and Testing, or on providing what it needs. Further detail
will be provided at least in part under TN LC10-020.*

.. todo::
   Add detail on restrictions to be applied to tested code, making clear that the burden
   is on the user to get this right, and not getting it right can invalidate the assumptions
   on which proof is based. To be completed in the Milestone 4 version of this document.

.. todo::
   Complete detail on combining formal verification and testing.
   To be completed in the Milestone 4 version of this document.

.. _code_policy:

Code Policies
~~~~~~~~~~~~~

The restrictions imposed on the subset of Ada that could be used in writing
SPARK 2005 programs were not simply derived from what was or is amenable to
formal verification. In particular, those restrictions stemmed partly from good
programming practice guidelines and the need to impose certain restrictions when
working in certain domains or against certain safety standards. Hence, we want
to allow such restrictions to be applied by users in a systematic and
tool-checked way despite the goal that |SPARK| embodies
the largest subset of Ada 2012 that is practical to formally verify.

Since |SPARK| will allow use of as large a subset of Ada 2012 as possible, this allows
for the definition of multiple *Code Policies* that allow different language
subsets to be used as opposed to the single subset given by SPARK 2005. Each of these
code policies can be targeted to meeting a specific user need, and where a user has multiple
needs then multiple policies may be enforced. Needs could be driven by:

- Application domains - for example, server-class information systems,

- Standards - for example, DO-178C Level A,

- Technical requirements - for example, systems requiring software that is
  compatible with a "zero footprint" run-time library.

As an example, a user developing an air traffic control system against DO-178C
might impose two code policies, one for the domain of interest and one for the
standard of interest.

These capabilities will be handled outside of the language since the need
is not specific to SPARK, and has already been resolved either by
Ada 2012 (pragma Restrictions and pragma Profile), or GNAT (pragma
Restriction_Warnings) or by coding standard checkers (e.g. gnatcheck).

.. todo::
   Complete detail on Code Policies.
   To be completed in the Milestone 4 version of this document.
   Consider referencing the User's Guide for details of the various profiles.

.. _ghost_entities:

Ghost Functions
~~~~~~~~~~~~~~~

Often extra entities, such as types, variables and functions may be required
only for test and verification purposes. Such entities are termed *ghost*
entities and their use should be restricted to places where they do not affect
the functionality of the program. Complete removal of *ghost* entities has no
functional impact on the program.

|SPARK| currently supports ghost functions but not ghost types or variables.
Ghost functions may be executable or non-executable. Non-executable ghost
functions have no implementation and can be used for the purposes of formal
verification only. Such functions may have their specification defined within an
external proof tool to facilitate formal verification. This specification is
outside of the |SPARK| language and toolset and therefore cannot be checked by
the tools. An unsound definition may lead to an unsound proof which is of no
use. Ideally any definition will be checked for soundness by the external proof
tools.

If the postcondition of a function, F, can be specified in |SPARK| as
F'Result = E, then the postcondition may be recast as the expression of an
``expression_function_declaration`` as shown below:

.. code-block:: ada

  function F (V : T) return T1 is (E);

The default postcondition of an expression function is F'Result = E making E
both the implementation and the expression defining the postcondition of the
function. This is useful, particularly for ghost functions, as the expression
which acts as the postcondition might not give the most efficient implementation
but if the function is a ghost function this might not matter.

.. _verific_modes:

Synthesis of |SPARK| Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

|SPARK| supports a *constructive* analysis style where all program units
require contracts specified by |SPARK| specific aspects to be provided on their
declarations. Under this constructive analysis style, these contracts have to
be designed and added at an early stage to assist modular analysis and
verification, and then maintained by the user as a program evolves. When the
body of a unit is implemented (or modified) it is checked that it conforms to
its contract. However, it is mandated that a |SPARK| analysis tool shall be able
to synthesize a conservative approximation of at least a minimum of |SPARK|
specific aspects from the source code of a unit.

Synthesis of |SPARK| aspects is fundamental to the analysis
of pre-existing code where no |SPARK| specific aspects are provided.

The mandatory requirements of a |SPARK| analysis tool is that it shall be
capable of synthesizing at least a basic, conservative :ref:`global-aspects`,
:ref:`depends-aspects` , :ref:`refined-global-aspect`,
:ref:`refined-depends-aspect`, :ref:`abstract-state-aspect`,
:ref:`refined_state_aspect` and :ref:`initializes_aspect` from either the
implementation code or from other |SPARK| aspects as follows:

  * if subprogram has no Depends aspect but has a Global aspect, an
    approximation of the Depends aspect is obtained by constructing a
    ``dependency_relation`` by assuming that all of the ``global_items`` that
    have a ``mode_selector`` of Output or In_Out are ``outputs``, those that
    have a ``mode_selector`` of Input or In_Out are ``inputs`` of the
    ``dependency_relation`` and that each ``output`` is dependent on every
    ``input``. This is a conservative approximation;

  * if a subprogram has a Depends aspect but no Global aspect then the Global
    aspect is determined by taking each ``input`` of the ``dependency_relation``
    which is not also an ``output`` and adding this to the Global aspect with a
    ``mode_selector`` of Input. Each ``output`` of the ``dependency_relation``
    which is not also an ``input`` is added to the Global aspect with a
    ``mode_selector`` of Output. Finally, any other ``input`` and ``output`` of
    the ``dependency_relation`` which has not been added to the Global aspect is
    added with a ``mode_selector`` of In_Out;

  * if neither a Global or Depends aspect is present, then first the globals of
    a subprogram are determined from an analysis of the entire program code.
    This is achieved in some tool dependent way. The globals of each subprogram
    determined from this analysis is used to synthesize the Global aspects and
    then from these the Depends aspects are synthesized as described above;

  * if an Abstract_State is specified on a package and a Refined_State aspect is
    specified in its body, then Refined_Global and Refined_Depends aspects shall
    be synthesized in the same way as described above. From the Refined_Global,
    Refined_Depends and Refined_State aspects the abstract Global and Depends
    shall be synthesized if they are not present.

  * if no abstract state aspect is specified on a package but it contains hidden
    state, then each variable that makes up the hidden state has a
    Abstract_State synthesized to represent it. At least a crude approximation of
    a single state abstraction for every variable shall be provided. A
    Refined_State aspect shall be synthesized which shows the constituents of
    each state.

  * If no Initializes aspect is specified for a package but it declares
    persistent variables which are initialized then an Initializes aspect shall
    be synthesized stating the visible variables that are initialized and the
    state abstractions representing the hidden variables that are initialized.

The syntheses described above do not include all of the |SPARK| aspects and nor
do the syntheses cover all facets of the aspects. In complex programs where
extra or more precise aspects are required they might have to be specified
manually.

An analysis tool may provide the synthesis of more aspects and more precise
synthesis of the mandatory ones.

Some use cases where the synthesis of aspects is likely to be required are:

- Code has been developed as |SPARK| but not all the aspects are included on all
  subprograms by the developer. This is regarded as *generative analysis*, where
  the code was written with the intention that it would be analyzed.

- Code is in maintenance phase, it might or might not have all of the |SPARK|
  specific aspects. If the aspects are present, the synthesized aspects may be
  compared with the explicit ones and auto correction used to update the aspects
  if the changes are acceptable. If there are aspects missing they are
  automatically synthesized for analysis purposes. This is also regarded
  as generative analysis.

- Legacy code is analyzed which has no or incomplete |SPARK| specific aspects
  This is regarded as *retrospective analysis*, where code is being analyzed
  that was not originally written with analysis in mind. Legacy code will
  typically have a mix of |SPARK| and non-|SPARK| code (and so there is an
  interaction with the detail presented in section :ref:`in_out`).
  This leads to two additional process steps that might be necessary:

  * An automatic identification of what code is in |SPARK| and what is not.

  * Manual definition of the boundary between the |SPARK| and non-|SPARK| code
    by explicitly specifying accurate and truthful contracts using |SPARK|
    specific aspects on the declarations of non-|SPARK| program units.

.. _in_out:

In and Out of |SPARK|
~~~~~~~~~~~~~~~~~~~~~

There are various reasons why it may be necessary to combine |SPARK| and
non-|SPARK| in the same program, such as (though not limited to):

- Use of language features that are not amenable to formal verification (and hence
  where formal verification will be mixed with testing).

- Use of libraries that are not written in |SPARK|.

- Need to analyze legacy code that was not developed as |SPARK|.

Hence, it must be possible within the language to indicate what parts are
(intended to be) in and what parts are (intended to be) out, of |SPARK|.

The default is to assume all of the program text is in |SPARK|, although this
could be overridden. A new aspect  *SPARK_Mode* is provided, which may be applied to a unit
declaration or a unit body, to indicate when a unit declaration or just its body
is not in SPARK and should not be analyzed. If just the body is not in |SPARK| a
|SPARK| compatible contract may be supplied on the declaration which facilitates
the analysis of units which use the declaration. The tools cannot check that the
the given contract is met by the body as it is not analyzed. The burden falls
on the user to ensure that the contract represents the behavior of the body as seen by the
|SPARK| parts of the program and -- if this is not the case -- the assumptions
on which the analysis of the |SPARK| code relies may be invalidated.

In general a definition may be in |SPARK| but its completion need not be.

A finer grain of mixing |SPARK| and Ada code is also possible by justifying
certain warnings and errors.  Warnings may be justified at a project, library
unit, unit, and individual warning level.
Errors may be justifiable at the individual error level or be
unsuppressible errors.

Examples of this are:

- A declaration occurring immediately within a unit might not be in, or might
  depend on features not in, the |SPARK| subset. The declaration might generate
  a warning or an error which may be justifiable. This does not necessarily
  render the whole of the program unit not in |SPARK|.  If the declaration
  generates a warning, or if the error is justified, then the unit is considered
  to be in |SPARK| except for the errant declaration.

- It is the use of the entity declared by the errant declaration, for instance
  a call of a subprogram or the denoting of an object in an expression
  (generally within the statements of a body) that will result in an
  unsupressible error. The body of a unit causing the unsuppressible (or
  declaration if this is the cause) will need to be marked as not in |SPARK| to
  prevent its future analysis.

Hence, |SPARK| and non-|SPARK| code may mix at a fine level of granularity.
The following combinations may be typical:

- Package specification in |SPARK|. Package body entirely not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|, with a small
  number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all bodies imported from another language.

- Package specification contains a mixture of declarations which are in |SPARK|
  and not in |SPARK|.  A client of the package may be in |SPARK| if it only
  references |SPARK| declarations; the presence of non-|SPARK| constructs
  in a referenced package specification does not by itself mean that
  a client is not in SPARK 2014.


Such patterns are intended to allow for mixed-language programming,
mixed-verification using different analysis tools, and mixed-verification
between formal verification and more traditional testing. A condition for
safely combining the results of formal verification with other verification
results is that formal verification tools explicitly list the assumptions that
were made to produce their results. The proof of a property may depend on the
assumption of other user-specified properties (for example, preconditions and
postconditions) or implicit assumptions associated with the foundation and
hypothesis on which the formal verification relies (for example,
initialization of inputs and outputs, or non-aliasing between parameters). When
a complete program is formally verified, these assumptions are discharged by
the proof tools, based on the global guarantees provided by the strict
adherence to a given language subset. No such guarantees are available when
only part of a program is formally verified.  Thus, combining these results
with other verification results depends on the verification of global and local
assumptions made during formal verification.

Full details on the SPARK_Mode aspect are given in the SPARK Toolset User's Guide (reference TBD).

.. todo::
   We need to consider what might need to be levied on the non-|SPARK| code in order for flow
   analysis on the |SPARK| code to be carried out.
   To be completed in the Milestone 4 version of this document.

.. todo::
   Complete detail on mixing code that is in and out of |SPARK|.
   In particular, where subheadings such as Legality Rules or Static Semantics are
   used to classify the language rules given for new language features, any rules
   given to restrict the Ada subset being used need to be classified in some way (for
   example, as Subset Rules) and so given under a corresponding heading. In addition,
   the inconsistency between the headings used for statements and exceptions needs
   to be addressed. To be completed in the Milestone 4 version of this document.

.. _volatile:

External State
~~~~~~~~~~~~~~

A variable or a state abstraction may be specified as external state to
indicate that it represents an external communication channel, for instance, to
a device or another subsystem. An external variable may be specified as volatile.
A volatile state need not have the same value between two reads without an
intervening update. Similarly an update of a volatile variable might not have any
effect on the internal operation of a program, its only effects are external to
the program. These properties require special treatment of volatile variables
during flow analysis and formal verification.

|SPARK| follows the Ada convention that a read of a volatile variable has a
possible side effect of updating the variable. |SPARK| extends this notion
to cover updates of a volatile variable such that an update of a volatile
variable also has a side effect of reading the variable. |SPARK| further extends
these principles to apply to state abstractions also using the Input_Only and
Output_Only options in the declaration of a state abstraction
(see section :ref:`external_state`).

.. _notes:

Notes on the Current Draft
--------------------------

The aim of this draft of the document is to fully define the main features of
the |SPARK| language. Subsequent updates for release 1 of the tools are only
expected to fix problems arising during implementation of the tools and correct
any errors in the document.

There are two areas of the language where there is on-going significant discussion
and so are likely to change. These areas are "Externals" and "Refined_Pre and Refined_Post".
