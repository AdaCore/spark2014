Introduction
============

|SPARK| is a programming language and a set of verification tools
designed to meet the needs of high-assurance software development.
|SPARK| is based on Ada 2012, both subsetting the language to remove
features that defy verification and also extending the system of
contracts by defining new Ada aspects to support modular, formal verification.

|SPARK| is a much larger and more flexible language than its
predecessor SPARK 2005. The language can be configured to suit
a number of application domains and standards, from server-class
high-assurance systems to embedded, hard real-time, critical systems.

A major feature of |SPARK| is the support of a mixture of test and proof which
facilitates the use of unit proof in place of unit testing; an approach now
formalized in DO-178C and the DO-333 formal methods supplement.
Certain units may be formally proven and other units validated through
testing.  Extra aspects are defined to support testing and the interface 
between tested and proven units.

The new aspects defined for |SPARK| all have equivalent pragmas which allows a
|SPARK| program to compiled by and executed by any Ada 2012 implementation.

The direct use of the new aspects requires an Ada 2012 compiler which supports them
in a way consistent with the definition given here in the |SPARK| reference manual.
The Gnat Pro Ada 2012 implementation is one such compiler.

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

- Section :ref:`reqts` gives an overview of the requirements given in this document
  over and above the language definition rules of the sort that appear in the
  Ada 2012 Reference Manual (RM).

- Section :ref:`sprs` defines the overall goals to be met by the |SPARK| language and
  toolset.

- Section :ref:`explain_sprs` provides expanded detail on the main strategic requirements.

- Section :ref:`generic_hlrs` presents language-independent requirements that are common to
  a number of the language features described in this document.

- Section :ref:`notes` provides some brief detail on the current status and contents
  of this document.


.. _lifecycle:

Lifecycle of this Document
--------------------------

This document will be developed incrementally towards a number of milestones,
culminating in Release 1 of the document that matches the first formal release
of the toolset. Subsequent releases of the document will follow, associated with
subsequent formal releases of the software. Hence, where inclusion of particular
scope is deferred, it may be deferred to:

- A specified milestone, meaning that the feature will be included in the first
  formal release of the toolset.

- A release subsequent to Release 1, meaning that the feature will be
  implemented *after* the first formal release of the toolset.

Note that the current content of this document may be subject to change
as the document is updated.

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
which section is specific to |SPARK|):

#. Syntax: this section gives the format of the |SPARK| aspects and pragmas.
   The expression defining the aspect and pragamas are specializations of the
   standard Ada 2012 expression syntax and will be accepted by any Ada 2012 
   implementation.

#. Legality Rules: these are rules that are enforced at compile time. A
   construct is legal if it obeys *all* of the Legality Rules.

#. Static Semantics: a definition of the compile-time effect of each construct.

#. Dynamic Semantics: a definition of the run-time effect of each construct.

#. Verification Rules: these rules define the proof and flow analysis checks
   to be performed on the language feature.

All sections are always listed and if no content is required then the
corresponding section will be marked *Not applicable*.

.. _formal_analysis:

Formal Analysis
---------------

|SPARK| will be amenable to a range of formal analyses, including but not limited to:

- Data-flow analysis, which considers the initialization of variables and the
  direction of data flow into and out of subprograms.

- Information-flow analysis, which also considers the coupling between the inputs
  and outputs of a subprogram. The term *flow analysis* is used to mean data-flow
  analysis and information-flow analysis taken together.

- Formal verification of robustness properties. In Ada terminology, this refers to
  the proof that certain predefined checks such as the ones which could raise 
  Constraint_Error, will never fail at run time and will never be raised.

- Formal verification of functional properties, based on contracts expressed as
  preconditions, postconditions, type invariants and so on.

The static checking needed to carry out this formal analysis is performed in three separate
phases and errors may be detected during any of these three steps. Firstly, the
legality rules presented in this document are checked together with
the Ada 2012 syntax and legality rules. Secondly, flow analysis is performed.
Rules enforced at this point are described in sections with the
heading "Verification Rules". Finally, formal program verification is performed.

Further Detail on Formal Verification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

Note that in some cases the result of performing formal verification may be
compiler or machine-dependent.
In such cases it must be possible to represent the dependencies as explicit
inputs to the formal verification process.


.. _dynamic_sem:

Dynamic Semantics of |SPARK| Programs
-------------------------------------

Every valid |SPARK| program is also a valid Ada 2012 program.
The dynamic semantics of the two languages are defined to be identical,
so that a valid |SPARK| program may be compiled and executed by means of
an Ada compiler.

Many invalid |SPARK| programs are also valid Ada 2012 programs.
An incorrect |SPARK| program with, say, inconsistent dataflow
annotations or undischarged proof obligations can still be executed as
long as the Ada compiler in question finds nothing objectionable.
What one gives up in this case is the formal analysis of the program,
such as proof of absence of run-time errors or the static checking of
dataflow dependencies.

SPARK 2014 may make use of certain aspects, attributes and pragmas
which are not defined in the Ada 2012 reference manual. Ada 2012
explicitly permits implementations to provide implementation-defined
aspects, attributes and pragmas.  If a |SPARK| program uses one
of these aspects (e.g., Global), or attributes (e.g., Update) then
it can only be compiled and executed by an implementation
which supports the construct in a way consistent with the definition
given here in the |SPARK| reference manual.

If the equivalent pragmas are used instead of the implementation-
defined aspects and if the use of implementation-defined attributes
is avoided, then a |SPARK| program may be compiled and executed
by any Ada 2012 implementation (whether or not it recognizes the
|SPARK| pragmas). Ada specifies that unrecognized
pragmas are ignored. The pragmas defined by |SPARK| either have
no dynamic semantics (e.g., pragma Global) or are used only to define
assertions whose success shall be proven statically (e.g., pragma
Loop_Variant). In either case, an Ada compiler which ignores the
pragma is correctly implementing the dynamic semantics of |SPARK| and
the |SPARK| tools will still be able to undertake all their static checks and proofs. 

.. _reqts:

Requirements Given in this Document
-----------------------------------

Detailed |SPARK| Language Definition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The detailed |SPARK| language definition is given in Ada terminology and
has two main components.  The first defines extensions to Ada 2012 in terms 
of new aspects, pragmas and attributes to provide |SPARK| features such as 
global specifications for subprograms.  The second defines a subset of Ada 2012 
by excluding certain language features. 
The exclusions, the new aspects, pragmas, attributes and rules specify the 
largest |SPARK| language for which formal analyses are supported. 

*Guidelines* may be applied which effectively reduce further the 
language subset which may be analyzed but may make analysis and proof easier, 
more precise and be suitable for some application areas (see :ref:`code_policy`).

Higher-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~

Higher-level requirements are given in non Ada specific terminology and have the
following structure:

#. Strategic requirements to be met by the |SPARK| language and its associated
   toolset (given in this chapter).

#. Requirements to provide particular language features.

#. For each such language feature, requirements are given to define how
   that feature should work in a way that is - as much as possible - language
   independent. [This means that language features may be understood independently
   of the low-level detail needed to make them work.]

Where relevant, a rationale will be given to explain why the requirement is
levied. Further narrative detail is given on each of the strategic requirements.

Since this detail does not strictly belong in this document then in future it
will be extracted and included in a new requirements document.


Presentation of Language Feature Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For each language feature, higher-level requirements are given under the following
headings:

#. *Goals to be met by language feature*: this defines the broad need behind
   a given language feature, along with requirements on the capabilities that
   the feature needs to support.

#. *Constraints*: this defines any ways in which we need to restrict the nature of
   the language feature, typically to serve the needs of analysis or verification.

#. *Consistency*: here, we consider the other language features being implemented
   and consider what the relationship should be between this and those features.

#. *Semantics*: here we define what the language feature means and hence
   what it means for the program to be correct against any specification given
   using this feature.

Reading these Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The higher-level requirements are naturally given in language that is less precise
than would be expected of rules in a language reference manual. Where greater
precision is required, that will be given in the language definition rules
themselves.

Generic Requirements
~~~~~~~~~~~~~~~~~~~~

A number of requirements apply to multiple language features and they are given
at the end of this chapter.


.. _sprs:

|SPARK| Strategic Requirements
------------------------------

The following requirements give the principal goals to be met by |SPARK|.
Some are expanded in subsequent sections within this chapter.

- The |SPARK| language subset shall embody the largest subset of Ada 2012 to which it is
  currently practical to apply automatic formal verification, in line with 
  the goals below, although future advances in verification research and 
  computing power may allow for expansion of the language and the forms of 
  verification available. See section :ref:`main_restricts`
  for further details.

- |SPARK| shall provide for mixing of verification evidence generated
  by formal analysis [for code written in the |SPARK| subset] and
  evidence generated by testing or other traditional means [for
  code written outside of the core |SPARK| language, including
  legacy Ada code, or code written in the |SPARK| subset for which
  verification evidence could not be generated]. See section :ref:`test_and_proof`
  for further details.

- |SPARK| shall provide support for constructive, generative and retrospective
  analysis as follows (see section :ref:`verific_modes` for further details):

   * |SPARK| shall support constructive (modular) specification, analysis and 
     verification of (partially) developed programs, to allow static analysis as
     early as possible in the development lifecycle. [Hence, package and
     subprogram bodies need not be present for formal verification to proceed.]
     
   * |SPARK| shall complete by generation from the body code, where possible, 
     incomplete contracts.  For instance, if a dependency relation is given on
     a subprogram but a subprogram nested within does not have a dependency 
     relation, it should be generated by the tools.  
     This may shorten development time and should simplify maintenance.

   * |SPARK| shall support retrospective analysis where useful
     forms of verification can be achieved with code that complies with the core 
     |SPARK| restrictions, but otherwise does not have any contracts.  
     Implicit contracts can be computed from the bodies of units, and then used
     in the analysis of other units, and so on.  Parts of the program which are
     not compliant with |SPARK| subset cannot be fully verified by the tools
     but a may be represented by a |SPARK| compatible contract at the unit level.
     
- *Code Policies* shall be allowed that reduce the subset of Ada 2012 that may
  be used in line with specific goals such as domain needs or certification
  requirements (these are similar to *Profiles* but may be imposed at a finer
  granularity and the effect of a breach may also be different). This may also
  have the effect of simplifying proof or analysis. See section
  :ref:`code_policy` for further details.

- |SPARK| shall allow the mixing of code written in the |SPARK| subset
  with code written in full Ada 2012. See section :ref:`in_out` for
  further details.
   
- |SPARK| shall support the development, analysis and verification of programs 
  which are only partly within the |SPARK| language and other parts in another
  language, for instance, full Ada or C. |SPARK| compatible contracts at unit
  level will form the boundary interface between the |SPARK| and other parts of
  the program. Many systems are not written in a single programming language and
  when retrospectively analyzing pre-existing code it may well not all conform to
  the |SPARK| subset. *No further detail is given in the current draft of this document on
  mixing |SPARK| code with non-Ada code.*

.. todo::
   Complete detail on mixing |SPARK| with non-Ada code.
   To be completed in the Milestone 3 version of this document.

- |SPARK| shall provide counterparts of all language features and analysis
  modes provided in SPARK 83/95/2005.

- Support for specifying and verifying properties of secure systems shall be improved.

- |SPARK| shall support provision of "formal analysis" as defined by DO-333, which states
  "an analysis method can only be regarded as formal analysis
  if its determination of property is sound. Sound analysis means
  that the method never asserts a property to be true when it is not true."
  Language features that defy sound analysis will be eliminated or their
  use constrained to meet this goal. See section :ref:`main_restricts` for further details.
  *Note that the current draft of this document does not necessarily  define
  all restrictions necessary to guarantee soundness.*

- The language shall offer an unambiguous semantics. In Ada
  terminology, this means that all erroneous and
  unspecified behavior shall be eliminated either by direct
  exclusion or by adding rules which indirectly guarantee
  that some implementation-dependent choice cannot effect
  the externally-visible behavior of the program. For example,
  Ada does not specify the order in which actual parameters
  are evaluated as part of a subprogram call. As a result of the
  SPARK rules which prevent the evaluation of an expression from
  having side effects, two implementations might choose different
  parameter evaluation orders for a given call but this difference
  won't have any significant effect. [This means implementation-defined
  and partially-specified features may be outside of
  |SPARK| by definition, though their use could be allowed and a warning or error 
  generated for the user. See section :ref:`in_out` for further details.]
  *Note that the current draft of this document does not necessarily  define
  all restrictions necessary to guarantee an unambiguous semantics.*

.. todo::
   Ensure that all strategic requirements have been implemented.

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

- Aliasing of names is not permitted.

- The goto statement is not permitted.

- The use of controlled types is not permitted.

- Tasking is not currently permitted (it is intended that this will be included
  in Release 2 of the tools).

- Raising and handling of exceptions is not permitted.


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

#. Formal verification is only cost-effective on a part of the codebase. (And
   it may be more cost-effective than testing on this part of the codebase.)

Since the combination of formal verification and testing cannot guarantee the
same level of assurance as when formal verification alone is used, the goal
when combining formal verification and testing is to
reach a level of confidence as good as the level reached by testing alone.

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
   on which proof is based. To be completed in the Milestone 3 version of this document.

.. todo::
   Complete detail on combining formal verification and testing.
   To be completed in the Milestone 3 version of this document.

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

- Application domains - for example, server-class air-traffic management systems,

- Standards - for example, DO-178C Level A,

- Technical requirements - for example, systems requiring software that is
  compatible with a "zero footprint" run-time library.

As an example, a user developing an air traffic control system against DO-178C
might impose two code policies, one for the domain of interest and one for the standard
of interest.

Since it should be possible to apply these policies  at multiple levels
of granularity - for example at a package level rather than at a library level -
and since it need not be the case that violation of one of these policies leads
to a compilation error, then the existing Ada mechanisms of pragma Restriction
and pragma Profile are not suitable. Hence, pragma Code_Policy will be introduced
as a counterpart to pragma Profile and pragma Guideline will be introduced
as a counterpart to pragma Restriction, meaning that a Code_Policy is a grouping
of Guidelines.

*No further detail is given in the current draft of this document on Code Policies.*

.. todo::
   Complete detail on Code Policies.
   To be completed in the Milestone 3 version of this document.

.. _verific_modes:

Constructive, Generative and Retrospective Analysis
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

SPARK 2005 strongly favored the *constructive* analysis style where all
program units required contracts to be provided on their specifications.  The
contracts are needed to perform in-depth static analysis and formal verification.
These contracts had to be designed and added at an early stage to assist modular 
analysis and verification, and then maintained by the user as a program evolved.
When the body is implemented (or modified) it is checked that it conforms to its 
contract.

However, some these contracts for a subprogram may be at least approximated from
its body, once implemented (provided the contracts of any subprograms it calls 
are specified or have already been generated), and so it is possible to 
implicitly synthesize from the body these contracts if they are not provided.  
The contracts can then be used in the analysis of calling subprograms and so on. 
In |SPARK| the contracts which may be synthesized from an implemented subprogram 
body are the global specification and the dependency relation.  
It may be possible to generate some of the package contracts also once the 
package body and its private dependents have been implemented.

Unlike the Global and Depends aspects used in flow analysis, the |SPARK| tools
will not attempt to automatically synthesize for a given subprogram body the
other aspects (i.e. Pre and Post), which define the subprogram's contract for
the purpose of formal verification.

There are three main use cases where generation of contracts are required:

- Code has been developed as |SPARK| but in order to reduce costs not all 
  the contracts are included on all subprograms by the developer.

- Code is in maintenance phase, it may or may not have complete contracts.
  If the contracts are complete, the generated contracts may be compared with 
  the given contracts and auto correction used to update the contracts if the
  changes are acceptable.
  If the contracts are incomplete they are automatically generated for analysis 
  purposes.
  
- Legacy code is analyzed which has no or incomplete contracts.

Hence, as well as still fully supporting the constructive development mode, 
|SPARK| is designed to facilitate the generation of contracts, which supports retrospective analysis.

Note that in the case where legacy code is being analyzed there may be a mix of
|SPARK| and non-|SPARK| code (and so there is an interaction with the detail
presented in section :ref:`in_out`). This leads to two additional process steps
that may be necessary:

- An automatic identification of what code is in |SPARK| and what is not.

- An annotation of the boundary between the |SPARK| and non-|SPARK| code with
  suitable |SPARK| compatible contracts. If this is not done then the analysis
  would have to assume some suitably conservative contract.

Note that when language features are presented and defined in the remainder of
this document, it is assumed that analysis and verification is being performed
constructively and no explicit detail is given on generative or retrospective
analysis.

*No further detail is given in the current draft of this document on
Constructive, Generative and Retrospective analysis and Verification.*

.. todo::
   Add detail on how retrospective analysis will work when we have a mix of |SPARK| and non-|SPARK|.
   To be completed in the Milestone 3 version of this document.

.. todo::
   Complete detail on constructive, generative and retrospective analysis and verification.
   To be completed in the Milestone 3 version of this document.

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
could be overridden. A new aspect is provided, which may be applied to a unit
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

The way in which these are used are:

- A construct appearing in a unit may not be in, or may depend on features not in, the 
  |SPARK| subset. The contract may generate a warning or an error which may be 
  justifiable. This does not necessarily render the whole of the unit as not in 
  |SPARK|.  If the construct generates a warning, or if the error is justified,
  then the unit is considered to be in |SPARK| except for the errant construct.

- It is the application of a construct which is not in |SPARK| 
  (generally within the statements of a body) that potentially moves the code 
  outside of the |SPARK| subset. An unsuppressible error will be generated and 
  the body containing the code will need to be marked as not in |SPARK| to 
  prevent its future analysis.
  
Hence, |SPARK| and non-|SPARK| code may mix at a fine level of granularity.
The following combinations may be typical:

- Package specification in |SPARK|. Package body entirely not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|, with a small
  number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all bodies imported from another language.

- Package specification contains a mixture of declarations which are in |SPARK|
  and not in |SPARK|.  A client of the package may be in SPARK 2014 if it only 
  references SPARK 2014 declarations; the presence of non-SPARK 2014 constructs
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

*No further detail is given in the current draft of this document on
mixing code that is in and out of SPARK 2014. Although there are a number of places where
a statement is given on what is in or out of SPARK 2014, that information is not yet complete
and nothing further is given on how it should be used.*

.. todo::
   We need to consider what might need to be levied on the non-|SPARK| code in order for flow
   analysis on the |SPARK| code to be carried out.
   To be completed in the Milestone 3 version of this document.

.. todo::
   Complete detail on mixing code that is in and out of |SPARK|.
   To be completed in the Milestone 3 version of this document.

.. _generic_hlrs:

Generic Language-Independent Requirements
-----------------------------------------

The following detail relates to higher-level requirements but applies to multiple
language features. Hence, it is given in a single place to ease readability.

Definition of Terms for Higher-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following terms are used in the presentation of the higher-level requirements;
each is intended to have a definition consistent with that when used in
language definition rules.

#. Hidden state: state declared within a package but that is not directly accessible
   by users of that package.

#. Inputs and outputs of a subprogram: the set of data items,
   including formal parameters, that may be read or written - either directly or indirectly - on a call
   to that subprogram.

#. Global data of a subprogram: the inputs and outputs of a subbprogram, other than the formal
   parameters.

#. Entire variable: a variable that is not a subcomponent of a larger containing variable.

#. Entity: the semantic object that represents a given declaration.


Abstract State, Hidden State and Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#. **Requirement:** When specifying properties of a subprogram, it shall be possible
   to refer to (an abstraction of) hidden state without knowing the details of that hidden state.

   **Rationale:** allows modular verification and also allows the management of
   complexity.

#. **Requirement:** It shall be possible to manage hierarchies of data abstraction [i.e. it shall be possible
   to manage a hierarchical organization of hidden state].
 
   **Rationale:** to allow modular verification and the management of complexity in the presence
   of programs that have a hierarchical representation of data.

Naming
~~~~~~

#. **Requirement:** Variable names in a global specification of a subprogram are 
   distinct from the formal parameter names of the subprogram .

   **Rationale:** A variable cannot be both a formal parameter and a global
   variable simultaneously.

#. **Requirement:** Names used in the new flow analysis specifications
   are distinct from local subprogram
   variables when both are in scope.  -- We may drop this rule and make it a 
   guideline

   **Rationale:** To avoid accidental hole in scope errors.

#. **Requirement:** Names used in the new flow analysis specifications
   shall refer to entire variables.

   **Rationale:** For the flow analysis model, updating part of a variable is regarded as
   updating all of it.

#. **Requirement:** Where distinct names are referenced within a given flow analysis specification, then
   those names shall refer to distinct entities.

   **Rationale:** to support flow analysis and to aid clarity of the interface definition.


Properties of Specifications
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#. **Requirement:** When specifying program behavior in terms of a relation or a set, it shall be
   possible to explicitly provide a null relation or an empty set.

   **Rationale:** to explicitly identify programs that - for example - do not reference
   global data. This is especially needed in the presence of retrospective analysis,
   where absence of a specification cannot mean presence of a null specification.

#. **Requirement:** It shall be possible to designate - both visible and hidden - state items that are Volatile
   and for each to give a mode of either in or out.

   **Rationale:** to model programs that refer to external state, since that state
   is modeled differently to internal state.

#. **Requirement:** When specifying subprogram behavior other than via proof statements
   -- such as global data -- it shall be necessary to provide a complete specification.

   **Rationale:** To allow provision of at least the same functionality and 
   error detection as SPARK 2005 and to allow modular analysis. 
   This is also necessary for security analysis.

.. _notes:

Notes on the Current Draft
--------------------------

This is an interim draft that covers all language-independent requirements
for the main language features, provides
syntax where possible and otherwise provides the detailed rules necessary to
support implementation of basic flow analysis. Where detail is not relevant to
meeting these needs then it has typically been removed, though a "ToDo" will indicate
that there is material still to be provided.

Note this means there are certain of the strategic requirements that are currently
not decomposed into language definition detail. Where this is the case, it will
have been explicitly indicated in this chapter.
