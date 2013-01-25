Introduction
============

|SPARK| is a programming language and a set of verification tools
designed to meet the needs of high-assurance software development.
|SPARK| is based on Ada 2012, both subsetting the language to remove
features that defy verification, but also extending the system of
contracts and "aspects" to support modular, formal verification.

|SPARK| is a much larger and more flexible language than its
predecessor SPARK 2005. The language can be configured to suit
a number of application domains and standards, from server-class
high-assurance systems (such as air-traffic management applications),
to embedded, hard real-time, critical systems (such as avionic
systems complying with DO-178C Level A).

How to Read this Manual
-----------------------

This language reference manual is *not* a tutorial guide
to |SPARK|.  It is intended as a reference guide for
users and implementors of the language.  In this context
"implementors" includes those producing both compilers and
verification tools.

This manual is written in the style and language of the Ada 2012 Reference Manual (RM),
so knowledge of Ada 2012 is assumed.  Chapters 2 through 13 mirror
the structure of the Ada 2012 RM.  Chapter 14 covers all the annexes
of the Ada RM.

Readers interested in how SPARK 2005 constructs and idioms map into
|SPARK| should consult the appendix :ref:`mapping-spec-label`.

Method of Description and Syntax Notation
-----------------------------------------

In expressing the syntax and rules of |SPARK|, the following chapters of
this document follow the notational conventions of the Ada 2012 RM (section 1.1.4).

High-level requirements
-----------------------

There are two main components to the SPARK 2014 LRM (this document). The first
defines an extension to the Ada 2012 syntax to provide SPARK features such
as dependency relations for subprograms. The second defines a subset of Ada
2012 by excluding certain language
features. The syntax and rules that define the extensions to the language must
be such that they work correctly given the Ada subset with which we are working
(and varying that subset will cause those rules to be modified: typically,
the stronger the restrictions on the Ada subset then the simpler will be the
SPARK rules, and vice versa).

However, the high-level requirements to be met by the SPARK 2014 language are invariant
under the scope of the Ada subset being used and are of necessity much simpler
to understand than the language definition rules. Moreover, they provide
a rationale for the language features and rules as provided in this document.

Hence, high-level requirements are provided according to the following
structure:

#. Strategic requirements to be met by the SPARK 2014 language and its associated
   toolset (given in this chapter).

#. Requirements to provide particular language features.

#. For each such language feature, requirements are given to define how
   that feature should work in a way that is - as much as possible - language
   independent. [This means that language features may be understood independently
   of the low-level detail needed to make them work in the context of the
   Ada 2012 subset being used.]

Where relevant, a rationale will be given to explain why the requirement is
levied. Further narrative detail is given on each of the strategic requirements.

Presentation of Language Feature Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For each language feature, high-level requiements are given under the following
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

Reading the High-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The high-level requirements are naturally given in language that is less precise
than would be expected of rules in a language reference manual. Where greater
precision is required, that will be given in the language definition rules
themselves.

Generic Requirements
~~~~~~~~~~~~~~~~~~~~

A number of requirements apply to multiple language features and they are given
at the end of this chapter.


|SPARK| Strategic Requirements
------------------------------

Principal design goals are as follows:

- Provision of "formal analysis" as defined by DO-333, which states
  "an analysis method can only be regarded as formal analysis
  if its determination of property is sound. Sound analysis means
  that the method never asserts a property to be true when it is not true."

- The language design shall support the case for soundness of analysis.
  Language features that defy sound analysis will be eliminated or their
  use constrained to meet this goal.

- The language shall offer an *unambiguous* semantics. In Ada terminology,
  this means that all erroneous and unspecified behaviour shall
  be eliminated. Implementation-defined features will be automatically
  determined for projects using GNAT, or will be configurable (where
  possible) or rejected for other compilers.

- The |SPARK| language subset shall embody the largest subset of Ada 2012 that is
  currently amenable to formal verification, in line with the goals above, although
  future advances in verification research and computing power may allow
  for expansion of the language and the forms of verification available.

- |SPARK| shall provide for both constructive and retrospective modes of
  verification.

- |SPARK| shall provide for mixing of verification evidence generated
  by formal analysis, for code written in the |SPARK| subset, and
  evidence generated by testing or other traditional means, for
  code written outside of the core |SPARK| language, including
  legacy Ada code, or code written in the |SPARK| subset for which
  verification evidence could not be generated.



Profiles and Analyses
---------------------

In addition to the core |SPARK| language subset, the language
may define a number of *Profiles* which are designed to meet
the needs of particular

- Application domains - for example, server-class air-traffic management systems,

- Standards - for example, DO-178C Level A,

- Technical requirements - for example, systems requiring software that is
  compatible with a "zero footprint" run-time library.

|SPARK| will be amenable to a range of formal analyses, including but not limited to:

- Data-flow analysis.

- Information-flow analysis and program slicing.

- Formal verification of robustness properties. In Ada terminology, this refers to
  the proof that a predefined check will never fail at run time, and hence predefined
  exceptions will never be raised.

- Formal verification of functional properties, based on contracts expressed as
  preconditions, postconditions, type invariants and so on.

- Formal verification of non-functional properties, such as WCET and
  worst-case memory usage analysis.

Principal Language Restrictions
-------------------------------

To facilitate formal verification, |SPARK| enforces a number of global
simplifications to Ada 2012. While these are covered in more detail
in the remaining chapters of this document, the most notable simplifications are:

- The use of access types and allocators is not permitted.

- All expressions (including function calls) are free of side-effects.

- Aliasing of names is not permitted.

- The goto statement is not permitted.

- The use of controlled types is not permitted.

- Tasking is not currently permitted.

- Raising and handling of exceptions is not permitted.

We describe a program unit or language feature as being "in |SPARK|"
if it complies with the restrictions required to permit formal
verification.  Conversely, a program unit language feature is "not in
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

Such patterns are intended to allow for mixed-language programming, and the development of programs
that mix formal verification and more traditional testing.

Static Checking
---------------

The static checking needed to determine whether a |SPARK|
program is suitable for execution is performed in three separate
phases. Errors may be detected during any of these three steps.

First, a compilation unit must compile successfully. In addition
to enforcing all of Ada's legality rules, |SPARK| imposes
additional restrictions (e.g., no uses of the reserved word
**access**). These additional restrictions are
described in sections with the heading "Extended Legality Rules".
A compilation unit might be fully in |SPARK|, partially in |SPARK|, or
not in |SPARK|, as instructed by the user, which sometimes determines
whether the compiler accepts it or not (e.g., a unit fully in |SPARK|
cannot use access types, while a unit partially in |SPARK| might).

Next, flow analysis is performed. For example, checks are performed that
the reads of and writes to global variables by a subprogram match the
behavior specified for the subprogram. Rules which are enforced at this
point are described in sections with the heading "Verification Rules"
and a subheading of "Checked by Flow Analysis".

.. note::
 (SB) this is silly - the heading should be "Flow Analysis Rules".
 The point is that there are no non-flow-analysis verification rules
 anymore. Everything else follows from the one rule that a run-time
 check induces a proof obligation. If we had ghost variables or
 prover-hints or something like that, then we might need
 "Verification Rules" sections. But we don't, so we don't.

.. note::
 (YM) I mostly agree with Steve... except for the possible case of
 type invariants. I don't know what's the status of type invariants in Ada
 2012, as there were some discussions not long ago that did not reach a
 final conclusion. The issue is whether type invariants are enforced at
 subprogram entry on IN parameters, or not. If it's not the case in Ada, we
 will still want to enforce this verification in SPARK, at least at the proof
 level. And, notewithstanding this issue, we will probably need to decide
 what to enforce for global variables read/written, and Ada RM does not say
 anything about this. Shouldn't this be under the "Proof Rules" or
 "Formal Verification Rules"?

Finally, formal program verification is performed.

Many Ada constructs have dynamic semantics which include a requirement
that some error condition must (or, in the cases of some bounded errors,
may) be checked, and some exception must (or, in the case of a bounded
error, may) be raised, if the error is detected (see Ada RM 1.1.5(5-8)). For
example, evaluating the name of an array component includes a check that
each index value belongs to the corresponding index range of the array
(see Ada RM 4.1.1(7)).

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

Every valid |SPARK| program is also a valid Ada 2012 program.
The dynamic semantics of the two languages are defined to be identical,
so that a valid |SPARK| program may be compiled and executed by means of
an Ada compiler.

Many invalid |SPARK| programs are also valid Ada 2012 programs.
An incorrect |SPARK| program with, say, inconsistent dataflow
annotations or undischarged proof obligations can still be executed as
long as the Ada compiler in question finds nothing objectionable. What one
gives up in this case is the formal proof of the absence of run-time errors,
the static checking of dataflow dependencies, and the formal proof that
the program implements its specifications (contracts and invariants).

There is an important caveat that must accompany the assertion that
|SPARK| is, in the sense described above, a subset of Ada 2012. |SPARK|
makes use of certain aspects, attributes, and pragmas that are not
defined in the Ada 2012 reference manual. Ada 2012 explicitly permits
implementations to provide implementation-defined aspects, attributes,
and pragmas. Whenever the |SPARK| manual defines an aspect (e.g.,
``Contract_Cases``), an attribute (e.g., ``Update``), or a pragma (e.g., ``Loop_Variant``),
this implies that a |SPARK| program which makes use of this
construct can only be compiled and executed by an
Ada implementation which supports this construct in a way that is
consistent with the definition given here in the |SPARK| reference manual.
The GNAT Pro Ada 2012 implementation is one such implementation.
The dynamic semantics of any construct other than these implementation-defined
attributes, aspects, and pragmas are defined to be as defined in the
Ada 2012 reference manual.

.. note::
 (SB) Need wording here to deal with the case where, to avoid duplication,
 the attribute/aspect/pragma definition occurs only in the GNAT RM.
 We have this situation already with Valid_Scalars attribute and more
 is on the way.

.. note::
 (SB) We could discuss other, more subtle cases in which SPARK
 is GNAT-dependent (e.g., intermediate overflow; elaboration order).
 That level of detail is probably inappropriate here.

Optional Restrictions and Profiles
----------------------------------

In addition to the global simplifications of the language given above, |SPARK|
defines a number of Restrictions that may be optionally applied to an entire
project, program or unit. These restrictions may provide additional simplification
of the language that users feel necessary, may meet particular demands of standards
or coding guidelines, and may facilitate additional forms of verification, or
may improve the level of automation achievable with existing analyses.

A *Profile* is a set of such Restrictions.

Constructive and Retrospective Verification Modes
-------------------------------------------------

SPARK 2005 strongly favoured the *constructive* verification style - where all
program units required contracts on their specifications.  These
contracts had to be designed and added at an early stage to assist modular
verification, and then maintained by the user as a program evolved.

In contrast, |SPARK| is designed to facilitate a more *retrospective* mode of
program construction and verification, where useful forms of verification can
be achieved with code that complies with the core |SPARK| restrictions, but
otherwise does not have any contracts.  In this mode, implicit contracts can be
computed from the bodies of units, and then used in the analysis of other
units, and so on.  These implicit contracts can be "promoted" by the user to
become part of the specification of a unit, allowing the designer to move from
the retrospective to the constructive mode as a project matures.  The
retrospective mode also allows for the verification of legacy code that was not
originally designed with the |SPARK| contracts in mind.

Combining Formal Verification and Testing
-----------------------------------------

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

Formal verification works by making some assumptions, and these assumptions
should be shown to hold even when formal verification and testing are
combined. Certainly, formal verification cannot guarantee the same
properties when part of a program is only tested, as when all of a program is
proved. The goal then, when combining formal verification and testing, is to
reach a level of confidence as good as the level reached by testing alone.

Any toolset that proposes a combination of formal verification and testing for
|SPARK| should provide a detailed process for doing so, including any necessary
additional testing of proof assumptions.




Definition of Terms for High-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ensure that if a term is the same or similar to one used in Aa then it means the
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


.. _generic_hlrs:

Generic high-level requirements
-------------------------------

The following high-level requirements apply to multiple language features and
hence are given in a single place to ease readability.

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

#. **Requirement:** Names declared and used in the new flow analysis specifications are distinct from formal parameters
   when both are in scope.

   **Rationale:** flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for the formal parameters
   of an enclosing subprogram.

#. **Requirement:** Names declared and used in the new flow analysis specifications
   are distinct from local subprogram
   variables when both are in scope.

   **Rationale:** flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for its local variables.

#. **Requirement:** Names declared and used in the new flow analysis specifications
   shall refer to entire variables.

   **Rationale:** For the flow analysis model, updating part of a variable is regarded as
   updating all of it.

#. **Requirement:** Where distinct names are referenced within a given flow analysis specification, then
   those names shall refer to distinct entities.

   **Rationale:** to support flow analysis and to aid clarity of the interface definition.


Properties of Specifications
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

#. **Requirement:** When specifying program behaviour in terms of a relation or a set, it shall be
   possible to explicitly provide a null relation or an empty set.

   **Rationale:** to explicitly identify programs that - for example - do not reference
   global data. This is especially needed in the presence of retrospective mode,
   where absence of a specification cannot mean presence of a null specification.

#. **Requirement:** It shall be possible to designate - both visible and hidden - state items that are Volatile
   and for each to give a mode of either in or out.

   **Rationale:** to model programs that refer to external state, since that state
   is modelled differently to internal state.

#. **Requirement:** It shall be possible to indicate for both visible and hidden state items
   a numeric integrity level.

   **Rationale:** to assist security and safety analysis.

#. **Requirement:** When specifying subprogram behaviour other than via proof statements, it shall be necessary
   to provide a complete specification.

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

Actions to complete prior to release
------------------------------------

#. Do we need more detail on refined pre and post-conditions? For example, how
   do we get post-conditions on functions used in proof contexts into those
   proof contexts?

#. Need to improve the rationale for the use of refined pre and post conditions.

#. Need to review the language feature HLRs for completeness: against 2005 LRM and initial draft
   will give this. The main thing to think about is visibility/getting certain information into
   certain aspects, such as proof aspects.

#. Make sure syntax is included where necessary (i.e. even where other details
   have been removed; where it is the same as some existing aspect, then add
   a comment to that effect).

#. Note that the semantics of the formal parameter modes is different to that of the global
   data items: what are the implications of this?

#. Trevor needs to check the requirements in relation to renaming.

#. Remove duplicate requirements.

#. Need to mention somewhere about being able to state volatile and mode characteristics
   for visible variables.

#. Put the Tobe Allocated reqts into the correct place.

#. Make sure all generic requirements from the scratch file are added in, making sure there is one
   relating to being able to provide abstraction.**

#. Add a generic requirement relating to simplicity: this will allow us to do things like
   state that names don't appear more than once in a given list, for example.

#. Remove references - other than in the Introduction - to whether things are
   in or out of SPARK and add a comment to say that that detail is still to
   be defined.

#. Do we need something in general on visibility? That is, an item where we state what
   a given language feature can refer to?

#. Note that we currently require from Global that outs are written on all executable paths,
   but nothing like that in relation to Depends.

#. Do I still need to add something on no overlapping between globals and formal parameter names,
   as well as names declared in the subprogram body? Where does that go (I thought I had something like that)?

#. Make stuff on future actions into ToDos: currently applies to Abstract State.

#. Get agreement on what we do with ToDos: i.e. do we leave them in or not: perhaps gather in
   a single list of possibilities for the future?

#. Check for consistency of all the high-level requirements.

#. Make sure that the high-level requirements are given with enough contextual detail.

#. Put the justification for presence of refined language features in this general
   section, since it is common for all.

#. Factor the strategic requirements below into this document. In particular, see
   what belongs here and what possibly belongs somewhere more general.

#. Note: need to check the rest of the introduction for possible additional
   strategic requirements.

#. Note: will need to make sure that every requirement traces down to something
   or that it doesn't need to.

#. Note: there is a possibility of tension between constructive and generative mode
   in that restrictions may be necessary to get the constructive mode to work that
   aren't necessary in generative mode (to an extent, that could be expected
   since the constructive mode has a tighter requirement).

#. Note: try to lift the level of abstraction of things like "distinct entities".

#. Note: handling retrospective, mixing of code and mixing of types of verification
    evidence might be difficult.

#. Make sure Flo captures any assumptions he is making as he constructs his graphs,
   as they will need to be reflected in the LRM.

#. Add something somewhere on prove once, use many times wrt generics (this should be derived from modularity
   and is also something for a subsequent release).

#. Need to make every strategic reqt traces to something (or if not understand why
   it shouldn't).

#. Should we present the high-level goals and the decomposed
   goals together (i.e. so we don't need the separate sections
   below).

#. Remember to get stuff from the SPARK book as well.

#. Remember also to be clear on the type of things we are stating (in particular,
   level of abstraction and also the thing on which the requirement is being levied).

#. Note that the Ada RM only applies to compilation, while ours applies to both
   analysis and compilation, but is meant to be built on top of the Ada RM.
   Do we need to make this clear and does this cause any problems? For example,
   rules in the Ada RM requiring bodies? Or does this just mean that our
   analysis mode has to be that we aren't compiling? Need to be clear on
   what is required for our analysis mode, and how that relates to what is
   levied in the RM (as we will certainly need some of what is in the Ada RM).

#. Need to distinguish language goals from project goals.

#. **To discuss with Flo: need to know the properties that need to hold
   of the graphs that he generates in order for everything to work (really, what
   are the pre-conditions to the analysis phase and to the graph generation phase).
   Note that when we add additional rules to the LRM, we are trying to avoid problems
   with soundness and we have Steve to help us with that: how are we guarding against
   this in the things that Flo does?**

#. Remove volatility from the detail for milestone 2, even in terms of those
   things where we don't give the language-specific rules. In general, go through
   and see what should be descoped.

#. **NB Need to define what is meant by imports and exports, wrt high-level
   requirements on Depends.**

#. We have a requirement to say that we provide everything that SPARK 2005 does:
   but at the very least we are missing --# accept and --# hide. Need to check to
   to see if there is anything else like this.


#. Need to define what semantics means: it should mean what needs to hold
   of the implementation so that it is considered correct against the specification.


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


#. Go through all the higher-level requirements and trace down to these where possible.



Strategic Requirements
~~~~~~~~~~~~~~~~~~~~~~

#. Note that need to classify the requirements here.

Provide rationale detail? I think that would be useful.

#. (A)|SPARK| shall provide counterparts of all language features and analysis
    modes provided in SPARK 2005.

#. (B) Provision of "formal analysis" as defined by DO-333, which states
   "an analysis method can only be regarded as formal analysis
   if its determination of property is sound. Sound analysis means
   that the method never asserts a property to be true when it is not true."

#. (C) The language design shall support the case for soundness of analysis.
   Language features that defy sound analysis will be eliminated or their
   use constrained to meet this goal.

#. (D) The language shall offer an unambiguous semantics. In Ada terminology,
   this means that all erroneous and unspecified behaviour shall
   be eliminated.

#. (E)Implementation-defined features will be automatically
   determined for projects using GNAT, or will be configurable (where
   possible) or rejected for other compilers.

#. (F)The |SPARK| language subset shall embody the largest subset of Ada 2012 that is
   currently amenable to formal verification - both proof and flow analysis -
   in line with the goals above, although future advances in verification
   research and computing power may allow for expansion of the language and
   the forms of verification available.

#. (G) Use paradigms shall be allowed that reduce the subset of Ada 2012 that may
   be used in line with specific goals such as domain needs or certification
   requirements. This may also have the effect of simplifying proof or analysis.

#. (H) |SPARK| shall allow for the specification of desired program behaviour in a modular
   fashion: need to know how this should interact with the requirement for
   modular verification.

#. (I) |SPARK| shall provide for a constructive (modular) mode of verification
   of (partially) developed programs, to allow static analysis as early as possible
   in the development lifecycle. [Hence, package bodies need not be present
   for formal verification to proceed.]

#. (J) |SPARK| shall provide a retrospective mode of verification that does not
   require presence of

#. (K) |SPARK| shall allow the mixing of code written in the |SPARK| subset
        with code written in full Ada 2012.

#. (L) |SPARK| shall provide for mixing of verification evidence generated
   by formal analysis [for code written in the |SPARK| subset] and
   evidence generated by testing or other traditional means [for
   code written outside of the core |SPARK| language, including
   legacy Ada code, or code written in the |SPARK| subset for which
   verification evidence could not be generated].

#. (M) Support for security shall be improved.

#. (N) Interfacing shall be allowed with non-SPARK code: was this meant to
       mean in terms of other languages or just in terms of non-SPARK Ada code.

#. (O) Ease of using the |SPARK| language shall be improved.

#. (P) It shall be possible to make use of the Ada Container library.

#. (Q) It shall be possible to represent any new language features as pragmas
   to allow compilation with pre-Ada 2012 compilers.

Notes on the Current Draft
--------------------------

This is an interim draft that covers all high-level requirements, provides
syntax where possible and otherwise provides the detailed rules necessary to
support implementation of basic flow analysis. Where detail is not relevant to
meeting these needs then it has typically been removed.


