
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
