Introduction
============

|SPARK| is a programming language and a set of verification tools
designed to meet the needs of high-assurance software development.
|SPARK| is based on Ada 2012, both subsetting the language to remove
features that defy verification and also extending the system of
contracts and "aspects" to support modular, formal verification.

|SPARK| is a much larger and more flexible language than its
predecessor SPARK 2005. The language can be configured to suit
a number of application domains and standards, from server-class
high-assurance systems to embedded, hard real-time, critical systems.

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

.. _read_interpret:

How to Read and Interpret this Manual
-------------------------------------

This LRM (language reference manual) is *not* a tutorial guide
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

Method of Description and Syntax Notation
-----------------------------------------

In expressing the syntax and rules of |SPARK|, the following chapters of
this document follow the notational conventions of the Ada 2012 RM (section 1.1.4).

The following sections are given for each new language feature introduced
for |SPARK|, following the Ada 2012 RM (other than *Verification Rules*, which is
specific to |SPARK|):

#. Syntax: this section gives the Syntax rules.

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

- Data-flow analysis, which considers the direction of data flow into and out
  of subprograms.

- Information-flow analysis, which also considers the coupling between the inputs
  and outputs of a subprogram. The term *flow analysis* is used to mean data-flow
  analysis and information-flow analysis taken together.

- Formal verification of robustness properties. In Ada terminology, this refers to
  the proof that a predefined check will never fail at run time, and hence predefined
  exceptions will never be raised.

- Formal verification of functional properties, based on contracts expressed as
  preconditions, postconditions, type invariants and so on.

The static checking needed to carry out this formal analysis is performed in three separate
phases and errors may be detected during any of these three steps. Firstly, the syntax 
and legality rules presented in this document are checked together with
the Ada 2012 syntax and legality rules. Secondly, flow analysis is performed.
Rules enforced at this point are described in sections with the
heading "Verification Rules". Finally, formal program verification is performed.

Further Detail on Formal Verification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Many Ada constructs have dynamic semantics which include a requirement
that some error condition must (or, in the cases of some bounded errors,
may) be checked, and some exception must (or, in the case of a bounded
error, may) be raised, if the error is detected (see Ada 2012 RM 1.1.5(5-8)). For
example, evaluating the name of an array component includes a check that
each index value belongs to the corresponding index range of the array
(see Ada 2012 RM 4.1.1(7)).

For every such run-time check (including bounded errors) a corresponding
obligation to prove that the error condition cannot be true is introduced.
In particular, this rule applies to the run-time checks associated with any
assertion (see Ada 2012 RM (11.4.2)); the one exception to this rule is pragma
``Assume`` (see :ref:`pragma_assume`).

In addition, the generation of proof obligations is unaffected by the
suppression of checks (e.g., via pragma ``Suppress``) or the disabling of
assertions (e.g., via pragma ``Assertion_Policy``). In other words, suppressing
or disabling a check does not prevent generation of its associated proof
obligations.

All such generated proof obligations must be discharged before the
formal program verification phase may be considered to be complete.


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

There is an important caveat, however, that must accompany the assertion that
|SPARK| is, in the sense described above, a subset of Ada 2012. |SPARK|
makes use of certain aspects, attributes, and pragmas that are not
defined in the Ada 2012 reference manual. Ada 2012 explicitly permits
implementations to provide implementation-defined aspects, attributes,
and pragmas. Whenever the |SPARK| manual defines an aspect (e.g.,
``Contract_Cases``), an attribute (e.g., ``Update``), or a pragma (e.g., ``Loop_Variant``),
this implies that a |SPARK| program which makes use of this
construct can only be compiled and executed by an
Ada implementation which supports this construct (in a way that is
consistent with the definition given here in the |SPARK| reference manual).

.. _reqts:

Requirements Given in this Document
-----------------------------------

There are two main components to the detailed language definition given in the
|SPARK| LRM (this document). The first
defines an extension to the Ada 2012 syntax to provide SPARK features such
as dependency relations for subprograms. The second defines a subset of Ada
2012 by excluding certain language
features. The syntax and rules that define the extensions to the language must
be such that they work correctly given the Ada subset with which we are working
(and varying that subset will cause those rules to be modified: typically,
the stronger the restrictions on the Ada subset then the simpler will be the
SPARK rules, and vice versa).

However, there are also higher-level requirements to be met by the |SPARK|
language that are invariant under the scope of the Ada subset being used and
that are of necessity much simpler to understand than the language definition rules. Moreover, they provide
a rationale for the language features and rules as provided in this document.

Hence, higher-level requirements are provided according to the following
structure:

#. Strategic requirements to be met by the |SPARK| language and its associated
   toolset (given in this chapter).

#. Requirements to provide particular language features.

#. For each such language feature, requirements are given to define how
   that feature should work in a way that is - as much as possible - language
   independent. [This means that language features may be understood independently
   of the low-level detail needed to make them work in the context of the
   Ada 2012 subset being used.]

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

- The |SPARK| language subset shall embody the largest subset of Ada 2012 that is
  currently amenable to automatic formal verification, in line with the goals below, although
  future advances in verification research and computing power may allow
  for expansion of the language and the forms of verification available. See section :ref:`main_restricts`
  for further details.

- |SPARK| shall provide for mixing of verification evidence generated
  by formal analysis [for code written in the |SPARK| subset] and
  evidence generated by testing or other traditional means [for
  code written outside of the core |SPARK| language, including
  legacy Ada code, or code written in the |SPARK| subset for which
  verification evidence could not be generated]. See section :ref:`test_and_proof`
  for further details.

- |SPARK| shall provide for constructive and retrospective modes of
  verification as follows (see section :ref:`verific_modes` for further details):

   * |SPARK| shall provide for a constructive (modular) mode of specification and verification
     of (partially) developed programs, to allow static analysis as early as possible
     in the development lifecycle. [Hence, package bodies need not be present
     for formal verification to proceed.]

   * |SPARK| shall provide a retrospective mode of verification where useful
     forms of verification can be achieved with code that complies with the core |SPARK| restrictions, but
     otherwise does not have any contracts.  In this mode, implicit contracts can be 
     computed from the bodies of units, and then used in the analysis of other
     units, and so on. 

- *Code Policies* shall be allowed that reduce the subset of Ada 2012 that may
  be used in line with specific goals such as domain needs or certification
  requirements (these are similar to *Profiles* but may be imposed at a finer
  granularity and the effect of a breach may also be different). This may also
  have the effect of simplifying proof or analysis. See section
  :ref:`code_policy` for further details.

- |SPARK| shall allow the mixing of code written in the |SPARK| subset
  with code written in full Ada 2012. See section :ref:`in_out` for
  further details.

- |SPARK| shall provide counterparts of all language features and analysis
  modes provided in SPARK 83/95/2005.

- Support for specifying and verifying properties of secure systems shall be improved.

- |SPARK| shall support provision of "formal analysis" as defined by DO-333, which states
  "an analysis method can only be regarded as formal analysis
  if its determination of property is sound. Sound analysis means
  that the method never asserts a property to be true when it is not true."
  Language features that defy sound analysis will be eliminated or their
  use constrained to meet this goal. See section :ref:`main_restricts` for further details.

- The language shall offer an *unambiguous* semantics. In Ada terminology,
  this means that all erroneous and unspecified behavior shall
  be eliminated. [This means implementation-defined and partially-specified features will be outside of
  |SPARK| by definition, though their use could be allowed and a warning generated for the user.
  See section :ref:`in_out` for further details.]

.. _explain_sprs:

Explaining the Strategic Requirements
----------------------------------------

The following sections provide expanded detail on the main strategic requirements.

.. _main_restricts:

Principal Language Restrictions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To facilitate formal verification, |SPARK| enforces a number of global
restrictions to Ada 2012. While these are covered in more detail
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

**Need to mention SPARK-friendly in here.**

**Action  LL-STT2: We need a term for the "SPARK-friendly" subset of features, which are not all in S14, but which allow for some amount of analysis.**


**Action comment REQ-CC56 (and look for TN referenced in associated action):  there is a missing discussion about what we used to call "alfa-friendly" code. I don't think we want to reuse this concept but
we need to define precisely what are the characteristics of a non-s14 subprogram that can call or be called by a s14 one so
that the formal verif on the latter be meaningful. We also want to minimize (eliminate?) the restrictions on Ada code that has
no influence on s14 code.**

**Associated action: Capture high-level information about how SPARK
2014 is intended to be used - probably in chapter
1. This needs to include "boundary issues" and assumptions about non-SPARK 2014 subprograms that are called from SPARK 2014. Boundaries exist between (1) spec in SPARK and body not in SPARK and (2) declarations not in SPARK cannot be used within a SPARK body. Open TN to record this discussion.**

There are common reasons for combining formal verification on some part
of a codebase and testing on the rest of the codebase:

#. Formal verification is only applicable to a part of the codebase. For
   example, it might not be possible to apply formal verification to Ada code
   that is not in |SPARK|.

#. Formal verification only gives strong enough results on a part of the
   codebase. This might be because the desired properties cannot be expressed
   formally, or because proof of these desired properties cannot be
   sufficiently automated.

#. Formal verification is only cost-effective on a part of the codebase. (And
   it may be more cost-effective than testing on this part of the codebase.)

For all these reasons, it is important to be able to combine the results of
formal verification and testing on different parts of a codebase.

Contracts on subprograms provide a natural boundary for this combination. If a
subprogram is proved to respect its contract, it should be possible to call it
from a tested subprogram. Conversely, formal verification of a subprogram
(including absence of run-time errors and contract checking) depends on called
subprograms respecting their own contracts, whether these are verified by
formal verification or testing.

Formal verification works by imposing requirements on the callers of proved code, and these requirements
should be shown to hold even when formal verification and testing are
combined. Certainly, formal verification cannot guarantee the same
properties when part of a program is only tested, as when all of a program is
proved. The goal then, when combining formal verification and testing, is to
reach a level of confidence as good as the level reached by testing alone.

Any toolset that proposes a combination of formal verification and testing for
|SPARK| should provide a detailed process for doing so, including any necessary
additional testing of proof assumptions.

*No further detail is given in the current draft of this document on Combining
Formal Verification and Testing.*

.. _code_policy:

Code Policies
~~~~~~~~~~~~~

The restrictions imposed on the subset of Ada that could be used in writing
SPARK 2005 programs was not simply derived from what was or is amenable to
formal verification. In particular, those restrictions stemmed partly from good programming practice
guidelines and the need to impose certain restrictions when working in certain domains
or against certain safety standards. Hence, we want to allow such restrictions to be
applied by users in a systematic and tool-checked way despite the goal that |SPARK| embodies
the largest subset of Ada 2012 that is amenable to formal verification.

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

.. _verific_modes:

Constructive and Retrospective Verification Modes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Action AN-JK4:   The generative contracts are mentioned very late in chapt. 6. It should
be stated that every subprogram has an implicit global/flow contract. If
the user provides one, both are compared and the implicit one should
refine the explicit one.
When the global/flow contract is required for analysis of another
subprogram (e.g. to implement the above comparison), the user-provided
contract is used if it exists, otherwise the implicit one is used.**

**Action  INSTRUCT-RPM1:  I'm a bit confused about how the SPARK 2014 language will provide for the mixing of verification evidence from code that is
within the 2014 subset and code that is outside of it. I can imagine a process where you do this, and have a mixture of 2014
and non-2014 code, and a mixture of formal verification and testing, but how does this influence the 2014 language itself?
Does it boil down to modularity and the ability to mix 2014 and non-2014 features at a fine level? I suppose the potential
confusion is that your whole "SPARK 2014" program may be a mixture of SPARK 2014 and non-SPARK 2014 code, but do you
still call the whole thing a SPARK 2014 program?**

SPARK 2005 strongly favored the *constructive* verification style -- where all
program units required contracts on their specifications.  These
contracts had to be designed and added at an early stage to assist modular
verification, and then maintained by the user as a program evolved.

As well as still fully supporting the cnstrucive mode, |SPARK| is designed
to facilitate a more *retrospective* mode of
program construction and verification, where useful forms of verification can
be achieved with code that complies with the core |SPARK| restrictions, but
otherwise does not have any contracts.  In this mode, implicit contracts can be
computed from the bodies of units, and then used in the analysis of other
units, and so on.  These implicit contracts can be "promoted" by the user to
become part of the specification of a unit, allowing the designer to move from
the retrospective to the constructive mode as a project matures.  The
retrospective mode also allows for the verification of legacy code that was not
originally designed with the |SPARK| contracts in mind.

*No further detail is given in the current draft of this document on
Constructive and Retrospective Verification Modes.*

.. _in_out:

In and Out of |SPARK|
~~~~~~~~~~~~~~~~~~~~~

**Note that our goal wrt this is just to make it more flexible (for example,
in or out defined by use and not be definition.**

**Action  FE-JIB12:  There are references throughout the document to being "in SPARK 2014" and "out of SPARK 2014". Since not being in SPARK
2014 is not an obstacle to compilation but in certain circumstances we may wish to enforce that only SPARK 2014 constructs are
used, then it is not clear from the LRM as it currently stands what should be done when implementing legality rules if a given syntactic
entity is found not to be in SPARK 2014.**

**Note that we need to state something about what it means when code is in SPARK: does it mean
that it is executable?**

**Need also to mention something about implementation-defined and partially-specified features and what could be done wrt those.**

**See if my separate section should be combined with this one.**

We describe a program unit or language feature as being "in |SPARK|"
if it complies with the restrictions required to permit formal
verification. **Action Stuart's comment on whether additional restrictions may
be imposed on top of this (REQ-SM12): I'm not sure what comes after the
"if" is true - there is more than this to the rationale for what is in the subset.**
Conversely, a program unit language feature is "not in
|SPARK|" if it does not meet these requirements, and so is not
amenable to formal verification. Within a single unit, features which
are "in" and "not in" |SPARK| may be mixed at a fine level. For
example, the following combinations may be typical:

- Package specification in |SPARK|. Package body entirely not in |SPARK|.

- Visible part of package specification in |SPARK|. Private part and body not in |SPARK|.

- Package specification in |SPARK|. Package body almost entirely in |SPARK|, with a small
  number of subprogram bodies not in |SPARK|.

- Package specification in |SPARK|, with all bodies imported from another language.

- Package specification contains a mixture of declarations which are in |SPARK| and not in |SPARK|.
  The latter declarations are only visible and usable from client units which are not in |SPARK|.
  **Action REQ-CC47: last bullet point, last sentence: that seems too strong a restriction for hybrid usage. I would prefer: the latter declarations
  are not used by pure SPARK 2014 code. I also think we need to define here what is the finest-grain of hybridation we are ready to deal
  with. In particular, a subprogram can only have 3 states:    - spec in S14, body not - spec and body outside of S14 - spec and body in S14
  we don't care about the case where the body would have chunks in s14 and other outside..**

Such patterns are intended to allow for mixed-language programming, and the development of programs
that mix formal verification and more traditional testing.

*No further detail is given in the current draft of this document on
mixing code that is in and out of |SPARK|.*

.. _generic_hlrs:

Generic Language-Independent Requirements
-----------------------------------------

The following detail applies to multiple language features and
hence are given in a single place to ease readability.

Definition of Terms for Language-Independent Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ensure that if a term is the same or similar to one used in Ada then it means the
same thing or we deliberately use a different term.

#. Hidden state.

#. Names.

#. Inputs and outputs.

#. Entire variables.

#. Entities.

#. Global data.

#. Mode.

#. Dependency relation: but note that the semantics definition basically gives this.

#. Package (since in theory we are being language-independent).

#. Refinement constituent.

#. Explain the *Abs* function introduced by state refinement.

Abstract State, Hidden State and Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#. **Requirement:** When specifying properties of a subprogram, it shall be possible
   to refer to (an abstraction of) hidden state without knowing the details of that hidden state.

   **Rationale:** allows modular verification and also allows the management of
   complexity.

#. **Requirement:** It shall be possible to manage hierarchies of data abstraction [i.e. it shall be possible
   to manage a hierarchical organisation of hidden state].

   **Rationale:** to allow modular verification and the management of complexity in the presence
   of programs that have a hierarchical representation of data.

Naming
~~~~~~

#. **Requirement:** Names used in the new flow analysis specifications are distinct from formal parameters
   when both are in scope.

   **Rationale:** flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for the formal parameters
   of an enclosing subprogram.

#. **Requirement:** Names used in the new flow analysis specifications
   are distinct from local subprogram
   variables when both are in scope.

   **Rationale:** flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for its local variables.

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
   global data. This is especially needed in the presence of retrospective mode,
   where absence of a specification cannot mean presence of a null specification.

#. **Requirement:** It shall be possible to designate - both visible and hidden - state items that are Volatile
   and for each to give a mode of either in or out.

   **Rationale:** to model programs that refer to external state, since that state
   is modelled differently to internal state.

#. **Requirement:** When specifying subprogram behavior other than via proof statements
   -- such as global data -- it shall be necessary to provide a complete specification.

   **Rationale:** To allow provision of at least the same functionality as SPARK 2005
   and to allow modular analysis. This is also necessary for security analysis.


To be allocated
~~~~~~~~~~~~~~~

#. (Proof) Need to be able to refer to Abstract State in proof contexts ("proof functions").
   Rationale: to allow proof to refer to hidden state for same reasons as Depends.

#. Optional guideline: detection of hole in scope: from good programming practice.

#. Trevor says there is a rule to say: Every refinement constituent should appear in at least one
   Global within that package Body. Where does that rule go and where is it in the
   2005 LRM?


.. _notes:

Notes on the Current Draft
--------------------------

**NB Need to be clear that not all of the strategic requirements flow down into
the document: in general, need to be clear on what is missing, since there
is lots of stuff not included in relation to the strategic requirements.**

This is an interim draft that covers all language-independent requirements
for the main language features, provides
syntax where possible and otherwise provides the detailed rules necessary to
support implementation of basic flow analysis. Where detail is not relevant to
meeting these needs then it has typically been removed.

Note this means there are certain of the strategic requirements that are currently
not decomposed into language definition detail. Where this is the case, it will
have been explicitly indicated in this chapter.

Actions to complete prior to release
------------------------------------

**NB Need to be clear that not all of the strategic requirements flow down into
the document.**

**NB For all the sections on strategic requirements, need to say at the end whether anything
is included on them in the document.**

**Associated action: LRM should not be GNAT-specific; references to GNAT should be removed.**

**Associated action:  In section 1.4 (Principal Language Restrictions) remove word "currently" from
Tasking bullet. Move comments/ToDos about rel2+ version of language to an appendix of future enhancements.**

#. Need to discuss the rationale for the use of refined pre and post conditions with people
   to make it better:

        * **Some of original detail:** Although an executable function may be used in defining an abstract pre-condition and
          then its definition will implicitly define the concrete pre-condition, the
          implementation of that function may be sufficiently complex that it is not easy
          to understand what it represents in the context of a pre-condition. Hence, that function
          would need a post-condition

#. Need to review the language feature HLRs for completeness: against 2005 LRM and initial draft
   will give this. The main thing to think about is visibility/getting certain information into
   certain aspects, such as proof aspects.

#. Make sure syntax is included where necessary (i.e. even where other details
   have been removed; where it is the same as some existing aspect, then add
   a comment to that effect).

#. Note that the semantics of the formal parameter modes is different to that of the global
   data items: what are the implications of this?

#. Trevor needs to check the requirements in relation to renaming.

#. Need to mention somewhere about being able to state volatile and mode characteristics
   for visible variables.

#. Put the Tobe Allocated reqts into the correct place.

#. Add a generic requirement relating to simplicity: this will allow us to do things like
   state that names don't appear more than once in a given list, for example.

#. Remove references - other than in the Introduction - to whether things are
   in or out of SPARK and add a comment to say that that detail is still to
   be defined.

#. Do we need something in general on visibility? That is, an item where we state what
   a given language feature can refer to?

#. Note that we currently require from Global that outs are written on all executable paths,
   but nothing like that in relation to Depends.

#. Make stuff on future actions into ToDos: currently applies to Abstract State.

#. Get agreement on what we do with ToDos: i.e. do we leave them in or not: perhaps gather in
   a single list of possibilities for the future?

#. Factor the strategic requirements below into this document. In particular, see
   what belongs here and what possibly belongs somewhere more general.

#. Note: need to check the rest of the introduction for possible additional
   strategic requirements.

#. Note: there is a possibility of tension between constructive and generative mode
   in that restrictions may be necessary to get the constructive mode to work that
   aren't necessary in generative mode (to an extent, that could be expected
   since the constructive mode has a tighter requirement).

#. Note: try to lift the level of abstraction of things like "distinct entities".

#. Add something somewhere on prove once, use many times wrt generics (this should be derived from modularity
   and is also something for a subsequent release).

#. Should we present the high-level goals and the decomposed
   goals together (i.e. so we don't need the separate sections
   below).

#. Remember to get stuff from the SPARK book as well.

#. Note that the Ada 2012 RM only applies to compilation, while ours applies to both
   analysis and compilation, but is meant to be built on top of the Ada 2012 RM.
   Do we need to make this clear and does this cause any problems? For example,
   rules in the Ada 2012 RM requiring bodies? Or does this just mean that our
   analysis mode has to be that we aren't compiling? Need to be clear on
   what is required for our analysis mode, and how that relates to what is
   levied in the RM (as we will certainly need some of what is in the Ada 2012 RM).

#. Need to distinguish language goals from project goals.

#. Remove volatility from the detail for milestone 2, even in terms of those
   things where we don't give the language-specific rules. In general, go through
   and see what should be descoped.

#. **NB Need to define what is meant by imports and exports, wrt high-level
   requirements on Depends.**

#. We have a requirement to say that we provide everything that SPARK 2005 does:
   but at the very least we are missing --# accept and --# hide. Need to check to
   to see if there is anything else like this.

#. Optional guideline: disallow use of different names for the same entities in the
   same subprogram.

#. Do we need flow analysis on contracts to check for uninitialized variables?
   This would only apply to pragmas.

#. General idea that we could pursue:

   * Define a simple standard relationship between refined global and global, but allow
     a feature to manually relate and justify. *In a way, this allows something like
     dual annotations but without needing two annotations.*

   * Similar for refinement of null state or caches in functions.

   * This is the idea of stepping outside of the language.

#. Explain what D1, D2 and rel2 actually mean.

#. Where Hristian said that certain rules have been deferred to the flow analyser, we need
   to move them to the appropriate sub-section in the LRM.

#. Describe the generative mode, rather than just retrospective.

#. Check through the derived SPRs to see if anything needs to be added from there.





