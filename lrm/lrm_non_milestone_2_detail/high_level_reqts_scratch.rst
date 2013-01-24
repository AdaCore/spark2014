General notes
=============

#. Remember to explain that sections of the document that aren't relevant have been removed for the moment.

High-level requirements
=======================

There are two main components to the SPARK 2014 LRM (this document). The first
defines an extension to the Ada 2012 syntax to provide SPARK features such
as Global. The second defines a subset of Ada 2012 by excluding certain language
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

#. Strategic requirements for the SPARK 2014 language (at a high level and
   possibly decomposed into .

#. Requirements to provide particular language features.

#. For each such language feature, requirements are given to define how
   that feature should work in a way that is - as much as possible - language
   independent. [This means that language features may be understood independently
   of the low-level detail needed to make them work in the context of the
   Ada 2012 subset being used.]

Where relevant, a rationale will be given to explain why the requirement is
levied. Further narrartive detail is given on each of the strategic requirements.

*Need to decide on a classification for the strategic requirements as well,
and the ones below them, where the latter includes use cases.*

*Need also to work out how to integrate the strategic reqts/high-level reqts
given independently of the language features, the use cases and the specific
detail on the language features.*

*Write up my model for what we are doing, including the stuff on domain, tool,
language extension, language subset: need to know what type of requirement artefact
is relevant for each entity we are referring to.*

*Note that the strategic requirements are really outside of our scope, though
they are still important.*

Notes
-----

#. NB This is taking a long time: need to make sure we get done what we need to
   by the time this draft needs to be done.

#. Note: need to check the rest of the introduction for possible additional
   strategic requirements.

#. Note: will need to make sure that every requirement traces down to something
   or that it doesn't need to.

#. Note: there is a possibility of tension between constructive and generative mode
   in that restrictions may be necessary to get the constructive mode to work that
   aren't necessary in generative mode (to an extent, that could be expected
   since the constructive mode has a tighter requirement).

#. Note: try to lift the level of abstraction of things like "distinct entities".

#. Note: Will need to add tracing between the various levels of requirements
    and identify where we can't trace.

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

Strategic Requirements
----------------------

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

Derived Strategic Requirements
------------------------------

In general, need to update wording that refers back to earlier rules or
have a better way of tracing.

#. DO-178C (DO-333): AH needs to ensure compliance here with whatever the Standard
   needs (but we need to know so we can feed it into the LRM).

#. Soundness:

   * Why3 model is sound.
   * The DGs and algorithms used on them must be sound.
   * Model of modular verification using aspects.
   * Language features chosen to be in or out: go through the 2005 LRM and identify
     why features are included or excluded; rely on Ada experts to identify
     corner cases.
   * If something can't be modelled satisfactorily then it has to be eliminated.
   * In order to show this we have to rely on review and test.

#. Retrospective: say that we will generate stuff that is missing though not
   always (i.e. we allow the rules to say that in some cases it means something
   that a given aspect is missing).

#. Unambiguous: wrt erroneous and unspecified, we could list the main ones; also
   check against the Ada RM.

#. Implementation-defined: check the Ada RM

#. Largest subset: will now effectively be covered by soundness.

#. Constructive (modular):

   * In general, this requires specifications on declarations.
   * Globals, to identify the complete interface...
   * Dependency relations on declarations for flow analysis.
   * Abstraction and refinement of data and proof.
   * Cannot mandate the presence of a body when doing (constructive) analysis.

#. Retrospective:

   * Synthesis of missing aspects from code where feasible.
   * Also the largest possible subset.

#. Mix of test and proof:

   * TBD

#. All current SPARK:

   * Check against the 2005 RM, excluding tasking and prove once/use many for generics.
   * Note that this may be a project requirement, in the sense it is a procedure
     to be carried out.

#. Largest subset goal:

   * "Guidelines" to be covered under here. Why not in their own right? I think they
     should be covered in their own right.

#. Support for security (wording to match rule above)

   * Information flow analysis.
   * Improve Integrity level model.
   * System-wide queries.
   * Program slicing.
   * Ability to transform from one security level to another.

#. Interfacing with non-SPARK code:

   * TBD

#. Executable semantics:

   * No decomposition necessary here.
   * Can step outside of this by specifying non-executable functions.

#. Ada Container library:

   * SPARK-friendly interface to existing library.
   * Want to avoid all things that could raise exceptions.
   * Specialized library: subset from the Ada Container library that are (potentially?)
     formally verified.
   * Are any of these Project requirements?

#. Ease of use improved:

   * Comes from bigger language subset.


Language Feature Requirements
-----------------------------

#. **To discuss with Flo: need to know the properties that need to hold
   of the graphs that he generates in order for everything to work (really, what
   are the pre-conditions to the analysis phase and to the graph generation phase).
   Note that when we add additional rules to the LRM, we are trying to avoid problems
   with soundness and we have Steve to help us with that: how are we guarding against
   this in the things that Flo does?**

#. Remove volatility from the detail for milestone 2, even in terms of those
   things where we don't give the language-specific rules. In general, go through
   and see what should be descoped.

#. What about volatile variables declared in the visible part of the spec,
   that hence don't appear in the abstract state aspect, and therefore that
   don't have a mode. Is it a change that we now don't want visible state in
   the abstract state aspect? Hence, perhaps we need a requirement that says
   volatile variables always need to have a mode, independently of where they
   are recorded.

#. In addition, need to talk to Trevor about the way the consistency relationship
   between concrete and abstract state is defined (in current LRM, defines it in large part
   by consistency between refined globals and depends and the abstract versions
   of those things, whereas I was going to define it at level of abstraction relationship
   and then apply it directly to the refined globals and depends).

#. We have a requirement to say that we provide everything that SPARK 2005 does:
   but at the very least we are missing --# accept and --# hide. Need to check to
   to see if there is anything else like this.

#. Need to have a definition of hidden state.

#. Wrt hierarchies of data refinement, do we need to make clear the conditions
   under which we can refine abstract state at one level onto abstract state at the lower
   level? Look at the 2005 LRM to see what it says.

#. Need to define what semantics means: it should mean what needs to hold
   of the implementation so that it is considered correct against the specification.

#. General: idea of replacing all renamings with the real thing prior to analysis.

#. General: the rule on referring to abstract state should be lifted up so that it
   refers to everything.

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

To be allocated
^^^^^^^^^^^^^^^

#. (Proof) Need to be able to refer to Abstract State in proof contexts ("proof functions").
   Rationale: to allow proof to refer to hidden state for same reasons as Depends.

#. Optional guideline: detection of hole in scope: from good programming practice.

#. Trevor says there is a rule to say: Every refinement constituent should appear in at least one
   Global within that package Body. Where does that rule go and where is it in the
   2005 LRM?

Definitions
^^^^^^^^^^^

#. Feature definition: this gives the use case and also gives the detail that would
   be present if we could give a mathematical definition.

#. Constraints: this defines any ways in which we need to restrict that definition
   or relation, typically to serve the needs of analysis or verification or because
   there is some language feature where the interaction with this feature
   is problematical. *Anything other than this? If not, this is very useful.*

#. Consistency: here, we consider the other language features being implemented
   and consider what the relationship should be between this and those features.

#. Semantics: here we define what the language feature means and hence
   what it means for the program to be correct against any specification given
   using this feature.


General
^^^^^^^

#. **NB Need to define what is meant by imports and exports, wrt high-level
   requirements on Depends.**

#. Names declared and used in the new language features are distinct from formal parameters
   when both are in scope. *Rationale: flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for the formal parameters
   of an enclosing subprogram.* Note that this is really language-dependent.

#. Names declared and used in the new language features are distinct from local subprogram
   variables when both are in scope. *Rationale: flow analysis is performed using names and so the analysis
   of a given subprogram should not depend on the names chosen for its local variables.*
   Note that this is really language dependent.

#. Names declared and used in the new language features shall refer to entire variables.
   *Rationale: For the flow analysis model, updating part of a variable is regarded as
   updating all of it.*

#. Go through all the higher-level requirements and trace down to these where possible.

#. It shall always be possible to explicitly specify the property of interest in the text
   of the program. *Give specific instantiations of this in relation to each of
   the language features?*
   *Rationale:*

   * To allow modular analysis.

   * To allow a developer to be prescriptive about the behaviour of the implementation.

   * To provide information to developers of client code about the behaviour of the subprogram
     prior to its implementation.

#. It shall be possible to refer to hidden state without knowing the details of
   that state.
   *Rationale: allows modular verification and also allows the management of
   complexity.*

#. It shall be possible to manage hierarchies of data abstraction [i.e. it shall be possible
   to manage a hierarchical organisation of hidden state].
   *Rationale: to allow modular verification and the management of complexity in the presence
   of programs that have a hierarchical representation of data.*
   Note that I need to think about whether this requirement stays at a high-level or gets incorporated into
   the specific detail: I think it has to stay at a high-level since how hierarchies are managed is more
   a language-specific thing.

Requirements on state declarations in general:

Abstract State
^^^^^^^^^^^^^^

#. Need to mention somewhere about being able to state volatile and mode characteristics
   for visible variables.



Initializes
^^^^^^^^^^^

#. *Note there are useful details in the 2005 LRM.*

#. Language feature:

   * This language feature defines the state initialized by a given package (or the
     state from that package that is initialized (during its elaboration)?).
     *This is a fundamental point that needs to be resolved, since it impacts
     how many of the rules are phrased.*

#. Feature definition (use cases?):

   * *TBD: do we need have a clear definition of what the set of things is
     that can be initialized vs what is the set of things on which that
     initialization can depend? I think we do, and we currently don't have that.*

   * *Original text:* They shall be able to refer to visible state and state abstractions from this package (these
     are exports). Rationale: to model programs.

   * *Original text:* They can also refer to visible state and state abstractions not declared in this package
     and on which initialization depends. Rationale: to model programs.

   * *TBD: what if an item of state in this package is initialized in another
     package? Then this aspect no longer specifies what from this package
     is intialized, rather it specifies what this package initializes: these
     two things used to be the same but now they aren't necessarly. Hence,
     I think we will need to impose a restriction even at this level
     if we want to do constructive analysis.*

   * It shall be possible to specify the complete set of state initialized
     by a given package during elaboration.
     *Rationale: To allow provision of at least the same functionality as SPARK 2005
     and to allow modular analysis. In addition, it allows a specifier to
     prescribe the state to be initialized and provides information to a developer
     on what he/she can expect to happen during elaboration of this package
     even if the package body has not yet been written.*

  * It shall be possible to state - for each item of state initialized by a given
    package - the other items of state on which that initialization depends.
    *Rationale: What is the rationale here?*

  * It shall be possible to indicate that state is initialized without dependence on
    any other state.
    *Rationale: to model programs.*

  * It shall be possible to indicate that no state in the package is initialized.
    *Rationale: to model programs.*

#. Constraints:

   * *TBD: need to decide if we have to constrain things or make assumptions
     in order to get this to work. However, the constraints would likely be upon
     the underlying language rather than on our new features.*

   * It shall not be possible to state that Volatile states are intialized [and hence
     it shall not be possible to actually initialize them.
     *8Rationale: initializing of volatile variables is disallowed.*


#. Consistency:

   * Not applicable.

#. Semantics:

   * The list of initialized state shall be complete.
     *Rationale: TBD this is necessary for ??? and most value is
     given if it is complete.*

   * *TBD: do we need to add detail in relation to the semantics in terms
     of executable paths, as per Depends?*

   * That (X,Y) is in the initializes relation for a given package
     (i.e. X depends on Y) means that X is intialized by the package
     such that the intial value of Y is used to set the final value of X on
     at least one executable path.
     *Rationale: by definition.* Note that this needs to be tidied up.

   * *TBD: plus need to add detail on the case that something is initialized
     without reference to anything else.*















Initializes Refinement
^^^^^^^^^^^^^^^^^^^^^^

#. General points:

   * There isn't much point in doing this until the actual Initializes detail
     is worked out.

   * The 2005 LRM has useful detail in relation to this.

   * The 2014 LRM isn't complete in the sense that it doesn't talk about
     the imports.

   * In general, the definition of the detail here should be similar to Depends.

#. Language feature:

#. Feature definition (use cases?):

   * This gives the definition of what is checked.

#. Constraints:

#. Consistency:

#. Semantics:

   * The basic definition of this can be given by the Abstraction function I
     defined for abstract state refinement.

#. Every state abstraction output of the Initializes clause has a refinement of
    which every constituent is initialized.

#. This language feature must be able to deal with the data abstraction hierarchy.

#. Every (output) variable from the visible part of the spec in an Initializes clause mst be initialized.

#. If something is not covered by the Initialization aspect then it is not initialized
   (unless it is volatile, etc).

#. If (X,Y) is in the Initializes relationship then X is intialized and its initialization
   depends on Y.

#. The ones above are about the meaning of the aspect and I think I can simplify that
   detail a lot.

#. (Volatile) Non-volatile constituents of volatile variables need to be initialzed,
    though without being dependent on anything.
    Rationale: it is implicit that the abstract version is initialized.

#. (Null) Must initialize constituents of null abstract state. Rationale: is
    implicit that the abstract version is initialized.
