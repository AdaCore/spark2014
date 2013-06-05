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

#. Need to go through all the text in this section to draw out stuff where there
   is an outstanding action but I haven't yet recorded it.

#. There are still issues to be resolved relating to refined pre- and post-conditions
   I think: the detail there doesn't feel very convincing and there isn't very much
   of it.

#. Need to go through and check that all terms are defined sufficiently well,
   so that the high-level requirements are sufficiently precise.

#. Remove volatility from the detail for milestone 2, even in terms of those
   things where we don't give the language-specific rules. In general, go through
   and see what should be descoped.

#. Note that we define requirements on augmentation plus subset, and then decompose
   as necessary (at least we do this notionally). This means that we might
   effectively get the final requirement at the language-independent level: hence,
   for the moment, we could note that but give a higher-level statement.

#. Details of global refinement with Contract_In have not yet been worked out
   (at least, they don't seem to be in the LRM).

#. What about volatile variables declared in the visible part of the spec,
   that hence don't appear in the abstract state aspect, and therefore that
   don't have a mode. Is it a change that we now don't want visible state in
   the abstract state aspect? Hence, perhaps we need a requirement that says
   volatile variables always need to have a mode, independently of where they
   are recorded.

#. Need to complete rationale detail wrt state refinement.

#. Need to define refinement wrtIntegrity levels.

#. In addition, need to talk to Trevor about the way the consistency relationship
   between concrete and abstract state is defined (in current LRM, defines it in large part
   by consistency between refined globals and depends and the abstract versions
   of those things, whereas I was going to define it at level of abstraction relationship
   and then apply it directly to the refined globals and depends).

#. Need to get definitions tidied up (e.g. abstract state, hidden state, etc).

#. We have a requirement to say that we provide everything that SPARK 2005 does:
   but at the very least we are missing --# accept and --# hide. Need to check to
   to see if there is anything else like this.

#. Need to have a definition of hidden state.

#. Wrt hierarchies of data refinement, do we need to make clear the conditions
   under which we can refine abstract state at one level onto abstract state at the lower
   level? Look at the 2005 LRM to see what it says.

#. General point: three types of refinement: state/data, type and proof, although only
   data refinement is of relevance here.

#. Need to define what semantics means: it should mean what needs to hold
   of the implementation so that it is considered correct against the specification.

#. Need to check the relevant sections against the 2005 LRM and also against the
   SPARK book.

#. Need to discuss in/out and Contract_In, in terms of what its semantics should
   be in relation to in/out.

#. Need to add rationale detail for the semantics for Global and Depends? Would be worth it.

#. General point: try to make all these consistent so apply to the rest what was done
   for the better ones.

#. *Need to think carefully here about what is required. Basically
need something at a high-level of abstraction but to which we can
trace all the LRM rules.*

#. General: idea of replacing all renamings with the real thing prior to analysis.

#. General: the rule on referring to abstract state should be lifted up so that it
   refers to everything.

#. Optional guideline: disallow use of different names for the same entities in the
   same subprogram.

#. Do we need flow analysis on contracts to check for uninitialized variables?
   This would only apply to pragmas.

#. A lot of the detail for Initializes is TBD.

#. Note that we need to think about reading/writing of Volatile variables during
   package elaboration: in what sense exactly?

#. Need to feed in Steve's comments on Package Initializes: in particular, stuff about
   being able to initialize stuff in different packages.

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

Abstract State
^^^^^^^^^^^^^^

#. Language feature:

    * This language feature provides an abstraction of the hidden state referenced by the package.

#. Feature definition (use cases?):

    * It shall be possible to provide an abstracted view of hidden state.
      *Rationale: allows modular analysis, since this means analysis performed before all package bodies are available
      and so before all hidden state is known. In addition, it allows management of complexity.*

    * It shall be possible to explicitly denote the absence of hidden state.
      *Rationale: to model programs without hidden state.*

    * It shall be possible to indicate those hidden state items that are Volatile
      and for each to give a mode of either in or out.
      *Rationale: to model programs that refer to external state, since that state
      has a different semantics to internal state.*

    * It shall be possible to indicate a numeric integrity level for each data item.
      *Rationale: to assist security and safety analysis.*

#. Constraints:

   * It shall not be possible to include visible state in the statement of abstract state.
     * Rationale: visible state is already visible in the necessary contexts and is not
     abstract.*
     *However, we may thus need a means of stating modes on visible volatile state.*

#. Consistency:

    * Not applicable.

#. Semantics:

    * Not applicable.


Global
^^^^^^

#. Language feature:

   * This language feature provides a list of the global data referenced by the
     subprogram.

#. Feature definition (use cases?):

   * It shall be possible to specify the complete list of global data used by a given subprogram.
     *Rationale:* To allow provision of at least the same functionality as SPARK 2005
     and to allow modular analysis. Plus ???*

   * It shall be possible to specify the mode (input, output or both)
     for each global data item.*Rationale: This matches the presentation of
     formal parameters, and the information is used by both flow analysis and proof.*

   * It shall be possible to identify globals that are only used in contracts.
     *Rationale: these are referenced by the subprogram but do not constitute a
     global in the usual sense.*

    * It shall be possible to explicitly denote the absence of use of global
      data. *Rationale: to model subprograms that do not access global data
      and since absence of a specification of global data usage cannot signify
      the absence of that usage, due to retrospective mode.*

#. Constraints:

   * The names used in a given list of global data items shall refer to distinct
     entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The list of global data for a given subprogram shall be complete.
     *Rationale: most value is given if the list is complete.*

#. Consistency:

   * Where a parameter at an enclosing scope is a global in this scope,
     formal parameter modes and global modes are consistent - i.e. an in out formal
     parameter can be either an in or an out global mode.
     *Rationale: allows an early basic consistency check.*

   * Where a global data list contains a volatile variable then the mode of
     the item in the global data list should match the mode of the item in the
     abstract state defintion.
     *Rationale: Accesses to volatile state should be consistent with their
     universal mode; moreover, note that volatile variables cannot have a
     mixed input/output mode.*
     * Note that this relies on volatile varables all appearing in the abstract
     state list.*

#. Semantics: *Need to sort out the detail in relation to Contract_In and in/out;
   and also add rationale detail.*


   * For each item in the list of global data for a given subprogram:
     * Need to check this detail carefully to make sure all cases are covered.
     And see if this detail could be abstracted. Note that I am assuming that if
     written once and read in a proof context then that is in out, so we need to
     make sure use of uninitalized variables is checked for proof contexts. If
     it isn't, then the output could be undefined on some paths. Also, what if assertions
     are turned off: need to make sure that we still do the check for unitialized
     variables regarding proof contexts even if they are.*

     * Note that it would be useful to do a table here of written (0, 1, all),
       read in non-proof context (0, 1, all), read in proof context (0, 1, all),
       plus column giving mode or error and then presenting it like that.

     * that - either directly or indirectly - is not written by the subprogram on
       any executable path but is read by the subprogram in a non-proof context
       on at least one executable path then that item shall have an input mode;

     * that - either directly or indirectly - is not read by the subprogram [in any context] on
       any executable path but is written by the subprogram on all executable paths
       then that item shall have an output mode;

     * that - either directly or indirectly - is not read [in any context] and is not written by the
       subprogram on any executable path, or is written once and not read on
       an executable path then an error shall be flagged.

     * that - either directly or indirectly - is read at least once [in any context] and
       written at least once by the subprogram on an executable path then that item shall
       have a combined input/output mode.

     * that - either directly or indirectly - is not read in a non-proof context and
       is not written by the subprogram on any executable path but is read in a proof
       context on an executable path, then that item shall have a mode indicating it is
       only used in contracts.

     * Do we need rationale detail here?

     * Note that if a proof read is used to determine whether in/out, then
       we lose the clear relationship with the dependency relation:
       alternatively, could we make the relevant value have nothing dependent on it?
       But in the case it has an impact on the program then its impact will
       be to terminate it, while the subprogram won't terminate. Hence,
       I think we shouldn't have in/out relate to use only in a proof context.
       Moreover, if we want to keep the Contract_In aspect then I think it should
       list everything that is used in the proofs, since normal usage by a subprogram
       is fundamentally different to usage in a proof context, at least terms
       of the possble outcomes.

Depends
^^^^^^^

#. Language feature:

   * This language feature defines the dependency relation met by a given
     subprogram, namely which exports are dependent on which inputs for a
     given subprogram (it gives the information flow).

#. Feature definition (use cases?):

   * It shall be possible to specify the complete dependency relation of a
     subprogram.
     *Rationale: To allow provision of at least the same functionality as SPARK 2005
     and to allow modular analysis. Plus ???*

   * It shall be possible to refer to both global data and formal parameters
     in the dependency relation.
     * Rationale: The imports and exports are given by both the global data and the
     formal parameters.*

   * It shall be possible to state where imports are not used or exports are
     derived from no import.
     *Rationale: to model programs accurately.*

   * It shall be possible to define an empty dependency relation.
     *Rationale: to model programs accurately.*

   * It shall be possible to assume an implicit dependency relation on functions
     and so an explcit statement shall not be required.
     *Rationale: this is typical usage and saves effort.*

#. Constraints:

   * The names used in a given dependency relation to define the exports
     of the subprogram shall refer to distinct entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The names used in a given dependency relation to define the inputs on which
     a given export depends shall refer to dinstinct entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The dependency relation shall be complete.
     *Rationale: this is necessary for security analysis and most value is
     given if it is complete.*

#. Consistency:

   * The dependency relation shall be consistent with the global data items and
     their modes in the following ways:

     * Every item in the list of global data associated with the subprogram that
       has either an output or input/output mode shall appear at least once as
       an export in the dependency relation.

     * Every item in the list of global data associated with the subprogram that
       has either an input or input/output mode shall appear at least once as
       an import in the dependency relation.

#. Semantics:

   * That (X,Y) is in the dependency relation for a given subprogram
     (i.e. X depends on Y) means that X is an export of the subprogram
     such that the intial value of Y is used to set the final value of X on
     at least one executable path.
     *Rationale: by definition.*


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


Refined Abstract
^^^^^^^^^^^^^^^^

#. Language feature:

   * This language feature allows an explicit statement of the hidden state declared
     in a package and the mapping of that hidden state to the state abstractions
     declared for the package.

#. Feature definition (use cases?):

   * It shall be possible to define for each state abstraction for the package the
     set of hidden state items that refine that abstract state (where the
     hidden state items can either be concrete state or further state abstractions).
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state,
     though nested abstraction is also necessary to manage hierarchies of data.*

   * It shall be possible to indicate those (refined) hidden state items that are Volatile
     and for each to give a mode of either in or out.
     *Rationale: to model programs that refer to external state, since that state
     has a different semantics to internal state.*

   * It shall be possible to indicate a numeric integrity level for each data item.
     *Rationale: to assist security and safety analysis.*

#. Constraints:

   * Each item of hidden state declared in the package must be mapped to exactly one abstraction.
     *Rationale: all hidden state must be covered since otherwise the appearance of abstract state
     in specifications provided by the user may be incomplete; that state must map to exactly one
     abstraction to give a clean and easily understandable abstraction, and for the purposes
     of simplicity of analysis.*

   * Each item of abstract state covered by the package shall be mapped to at least one
     item of hidden state (either concrete state or a further state abstraction).
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state.*

#. Consistency: the following detail is taken from the 2005 LRM. Further modifications to this detail
   are not made yet since they depend on how exactly volatile variables are to be modelled
   and the different cases that need to be modelled.

   * Abstract state may not be mapped to (volatile) hidden state that is of input/output mode.
     *Rationale: TBD.*

   * A volatile abstract state item may be mapped to a mix of volatile and non-volatile
     hidden state items. *Is this currently allowed in SPARK?*
     *Rationale: to allow the appropriate abstraction of complex i/o devices.*

   * If a volatile hidden state item is mapped to a volatile abstract state item, it must have
     the same mode as the abstract state item.
     *Rationale: TBD.*

   * A non-volatile abstract state item can be mapped to either volatile - of any mode - or non-volatile
     hidden state. *Is this not a potential security leak? Is this currently in SPARK 2005*
     *Rationale: TBD.*

   * Where an abstract state item is mapped to another (volatile) abstract state item albeit at a lower
     level of abstraction, the mode of the second item must be the same in the refinement mapping and in the
     declaration of that lower-level abstract state.
     *Rationale: TBD.*

   * Does a volatile variable have to map onto at least one volatile variable in SPARK 2005?

   * *TBD: Rules for refinement of Integrity levels.*

#. Semantics:

   * Covered under constraints (the only thing to include would have been how the
     aspect relates to the implementation, which is purely to do with hidden
     state appearing in there).

#. Possible detail for the future:

   * It shall be possible to refine null abstract state onto hidden state.
     *Rationale: this allows the modelling of programs that - for example - use caches
     to improve performance.*

   * It shall be possible to refine abstract onto hidden state without any restrictions,
     but the refinement will be checked and potential issues flagged up to the user.
     *Rationale: there are a number of different possible models of mapping abstract
     to concrete state - especially when volatile state is being used - and it might
     be useful to provide greater flexibility to the user. In addition, if a facility is
     provided to allow users to step outside of the language then it may be
     necessary to relax the abstraction model as well as relaxing the language feature
     of direct relevance.*

   * It shall be possible to refine volatile abstract state onto concrete volatile state
     of differing modes.
     *Rationale: TBD*


Refined Global
^^^^^^^^^^^^^^

#. *TBD: do I need to explicitly say what data items the refined data list can
   refer to?*

#. Language feature:

   * Where a global data list referring to abstract state has been specified for a subprogram,
     this allows the refinement of that global data list according to the refinement of that
     abstract state.

#. Feature definition (use cases?):

   * Where a global data list referring to abstract state has been specified for a subprogram,
     it shall be possible to provide a refined global data list that takes account of the
     refinement of that abstract state.
     *Rationale: the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state,
     though nested abstraction is also necessary to manage hierarchies of data.*
     * Why do we need this syntax? It doesn't help us with modular analysis,
     does it? Need to discuss this. Does it make it easier for the developer? I think
     it only makes it easier for the developer if he/she can hide the body of the
     subprogram being developed and then he/she at least gets a check of the concrete
     against the abstract. Note that we may still want to specify what exactly is used and how. *

   * It shall be possible to specify the mode (input, output or both)
     for each refined global data item.*Rationale: This matches the presentation of
     formal parameters, and the information is used by both flow analysis and proof.*

   * It shall be possible to identify refined globals that are only used in contracts.
     *Rationale: these are referenced by the subprogram but do not constitute a
     global in the usual sense.*

    * It shall be possible to explicitly denote the absence of use of global
      data. *Rationale: to model subprograms that do not access global data
      and since absence of a specification of global data usage cannot signify
      the absence of that usage, due to retrospective mode.*

#. Constraints:

   * The names used in a given list of global data items shall refer to distinct
     entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The list of global data for a given subprogram shall be complete.
     *Rationale: most value is given if the list is complete.*

#. Consistency:

   * Where a refined global data list contains a volatile variable then the mode of
     the item in the refined global data list should match the mode of the item in the
     refined state defintion.
     *Rationale: Accesses to volatile state should be consistent with their
     universal mode; moreover, note that volatile variables cannot have a
     mixed input/output mode.*
     * Note that this relies on (concrete) volatile varables all appearing in the refined
     state list.*

   * Relationship with global:

     * Need to have consistency with state refinement in terms of how we
       refine volatile variables: actually, I think we get this by requiring
       consistency at the non-refined level with abstract state and consistency at the
       refined level with refined state. *But thought needs to be put in to make sure
       it will all work consistently. For example, are we sure the way volatile refinement
       is managed doesn't have an impact here?*

     * The basic approach used here will be the text from p.57 of the 2005 LRM
       (the two paragraphs that start "A refinement G'").
       *Are there needs to which this precise way of doing refinement of globals
       actually maps?*

     * Plus - where the 2005 detail differs from the current 2014 detail - will need
       to understand why it was different (i.e. what was the goal).

     * In addition, we will need detail on how Contract_In is going to map:
       If a singleton refinement, then retain Contract_In.
       If any of the other relevant refinement constituents map to anything
       other than Contract_In then do we ignore it? What about it contributing
       to an in out?

#. Semantics:

   * As per Global.

#. Possible detail for the future:

   * If it is possible to refine null abstract state, then refinements of such
     state could appear in refined globals statements, though they would need
     to have mode in out.


Refined Depends
^^^^^^^^^^^^^^^

#. *TBD: check against the definition of Refined Global and make sure
   everything is covered here that they have in common.*

#. Language feature:

   * Where a dependency relation referring to abstract state has been specified for a subprogram,
     this allows the refinement of that dependency relation according to the refinement of that
     abstract state.

#. Feature definition (use cases?):

   * Where a dependency relation referring to abstract state has been given,
     it shall be possible to specify a refined dependency relation that takes account
     of the refinement of that abstract state.
     *Rationale: TBD: need to discuss with Trevor. See the comments on
     Refined Global. Is the rationale that we still want to to be able to specify what
     is done at the correct level of detail, since the high-level statement
     doesn't fully define the concrete dependency-relation?*

   * It shall be possible to refer to both global data and formal parameters
     in the refined dependency relation.
     * Rationale: The imports and exports are given by both the global data and the
     formal parameters.*

   * It shall be possible to state where imports are not used or exports are
     derived from no import.
     *Rationale: to model programs accurately.*

   * It shall be possible to define an empty refined dependency relation.
     *Rationale: to model programs accurately.*

   * It shall be possible to assume an implicit refined dependency relation on functions
     and so an explcit statement shall not be required.
     *Rationale: this is typical usage and saves effort.*

#. Constraints:

   * The names used in a given refined dependency relation to define the exports
     of the subprogram shall refer to distinct entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The names used in a given refined dependency relation to define the inputs on which
     a given export depends shall refer to distinct entities.
     *Rationale: to support flow analysis and to make the interface definition clear.*

   * The refined dependency relation shall be complete.
     *Rationale: this is necessary for security analysis and most value is
     given if it is complete.*

#. Consistency:

   * The refined dependency relation shall be consistent with the refined global data items and
     their modes in the following ways:

     * Every item in the list of refined global data associated with the subprogram that
       has either an output or input/output mode shall appear at least once as
       an export in the refined dependency relation.

     * Every item in the list of refined global data associated with the subprogram that
       has either an input or input/output mode shall appear at least once as
       an import in the refined dependency relation.

  * Relationship with Depends:

    * See pp.57-58 in the 2005 LRM for a definition of how this works.
      *Are there needs to which this precise way of doing refinement of depends
      actually maps?*

    * Plus - where the 2005 detail differs from the current 2014 detail - will need
      to understand why it was different (i.e. what was the goal).

    * Plus will need to make this work for Volatile variables, in case the way they
      are modelled has any impact here. I don't think there is impact here though.

    * Plus will need to change in view of the fact that - as far as I know - previously
      concrete variables were also covered by the own variable annotation.

#. Semantics:

   * As per Depends.

#. Possible detail for the future:

   * If it is possible to refine null abstract state, then refinements of such
     state could appear in refined depends statements, but wouldn't map to
     anything in the depends relation itself and would need to have mode in/out
     in the refined depends.


Refined Pre/Post-condition
^^^^^^^^^^^^^^^^^^^^^^^^^^

#. *Any further detail needed under here?*

#. Language feature:

   * *TBD*

#. Feature definition (use cases?):

   * Where a pre- or post-condition (referring to abstract state?) has been provided
     for a subprogram declaration, it shall be possible to state a refined
     pre- or post-condition that refers to concrete rather than abstract state
     and/or concrete rather than abstract type detail.
     *TBD: need to get agreement that this is what the need is; and also make
     sure the rationale is watertight, since it is likely to invite controversy.*
     *Rationale:*

        *  At the abstract level, we can only define symbols and not meaning.
           *This isn't strictly true, cf sets, etc, though model of them not in SPARK.*

        * It is possible to define symbols via executable code.

        * But the executable code may be complex so that it itself needs a specification.

        * But we can't use Pre and Post on the body.

        * So we introduce Refined Pre and Post.

        * We have the principle in Ada that it is clear about what is being done:
          since we are performing refinement then we should be (able to be) clear about that.

        * We are still doing refinement even if we don't have the syntactic labels.

        * *Note that this is an Ada-specific justification (though in general we have
          decided it is better to have Refined_X for all of the types of specification
          we use.*

        * *TBD: do we have semantics for how pre- and post-conditions on functions
          used in proof contexts actually feed into the proof we are doing? In general,
          I think there are still details to be worked out here, or at the very
          least more detail needs to be provided in the text.*

#. Constraints:

   * *TBD: is there anything to say here? We didn't discuss anything.*

#. Consistency:

   * The refined pre-condition must be implied by the pre-condition and the
     refined post-condition must imply the post-condition.
     *Rationale: standard definition of proof refinement.*
     *TBD I assume we don't need to say anything about abstracting data or
     abstracting types.*

#. Semantics:

   * Not applicable (defined via the semantics of pre and postconditions?)

   * *TBD: note that we need to decide how exactly this is all going to work:
     for example, the semantics here depends on whether these statements
     are executable. Plus it depends on whether it still contains state
     abstraction information, and on how exactly that information is presented.*

#. Further notes:

   * Proof refinement has to take both data and type refinement into account.
     *TBD: does this have any further implications?*


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
