Introduction
============
This file is a parking lot for the high-level requirements from the LRM. These may be re-introduced into the LRM introduction at a future issue or placed in a separate document. 

A general update of the requirements is still required to bring them in-line with other changes since Release 0.2.

Section headings have been left in to preserve the context of the high-level requirements sections (but numbering may not co-incide at lowest level as empty sections have not been included). Some empty sections appear in order to preserve the context of cross references.

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

*Code Policies* may be applied which effectively reduce further the
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
   of the low-level details needed to make them work.]

Where relevant, a rationale will be given to explain why the requirement is
levied. Further narrative detail is given on each of the strategic requirements.

Since this detail does not strictly belong in this document in future it
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
precision is required, this will be given in the language definition rules
themselves.

|SPARK| Strategic Requirements
------------------------------

Explaining the Strategic Requirements
----------------------------------------

.. _ghost_entities:

Ghost Entities
~~~~~~~~~~~~~~

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

#. *Hidden state*: state declared within a package but that is not directly accessible
   by users of that package.

#. *Inputs and outputs of a subprogram*: the set of data items
   that may be read or written - either directly or indirectly - on a call
   to that subprogram.

#. *Global data of a subprogram*: the inputs and outputs of a subprogram minus the formal
   parameters.

#. *Entire variable*: a variable that is not a subcomponent of a larger containing variable.

#. *Entity*: the semantic object that represents a given declaration.

.. _state_abstraction_and_hidden_state:

State Abstraction, Hidden State and Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
   shall refer to entire variables.  Within a subprogram body flow analysis will 
   operate at an individual subcomponent level for objects of a record type.

   **Rationale:** For the flow analysis model at the inter-subprogram level, 
   updating part of a variable is regarded as updating all of it.
   Within a subprogram body the subcomponents of a record type object
   are tracked individually.

#. **Requirement:** Where distinct names are referenced within a given flow 
   analysis specification, then those names shall refer to distinct entities.

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


Lexical Elements
================

Declarations and Types
======================

Names and Expressions
=====================

Statements
==========

Loop Statements
---------------

Loop Invariants, Variants and Entry Values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language features:

    * **Requirement:** |SPARK| shall include feature/s to support proof of loop termination.

      **Rationale:** To aid detection of a serious programming error.

    * **Requirement:** |SPARK| shall include feature/s to support proof of correctness
      of code containing loops.

      **Rationale:** To support proof.

   * **Requirement:** Within a loop, it shall be possible to refer to the value of a given
     variable on entry to that loop.

     **Rationale:** To support proof.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable


Proof Statements
----------------

High-Level Requirements
~~~~~~~~~~~~~~~~~~~~~~~

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible for users to explicitly state assumptions
      within the text of a subprogram to support the formal verification of that subprogram.

      **Rationale:** This allows facts about the domain to be used in a proof in a clean
      and explicit way.

   * **Requirement:** It shall be possible for users to assert at a given point within
     a subprogram the minimum set of facts required to complete formal verification
     of that subprogram.

     **Rationale:** This allows an explicit statement of what is necessary to complete
     formal verification and also assists the efficiency of that verification.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable


Subprograms
===========

Subprogram Declarations
-----------------------

Contract Cases 
~~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify pre- and post-conditions
     in a concise way in the case that subprogram behaviour is specified in
     terms of what behaviour should be in each of a series of mutually-independent cases.

     **Rationale:** To provide a more structured way of specifying subprogram behaviour.

#. Constraints, Consistency, Semantics, General requirements:

    * Not applicable

Global Aspects
~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify the list of global data read and updated
     when the subprogram is called. [Note that the data read can include data
     used in proof contexts, including assertions.]

     **Rationale:** to allow provision of at
     least the same functionality as SPARK 2005 and to allow modular analysis.

   * **Requirement:** It shall be possible to specify the mode (input, output or both)
     for each global data item.

     **Rationale:** This matches the presentation of
     formal parameters, and the information is used by both flow analysis and proof.

   * **Requirement:** It shall be possible to identify globals that are used only in proof contexts.
     
     **Rationale:** since the list of global data items constrains the data that can be read
     and updated when the subprogram is called, then the global data list needs to cover
     data items that are read in proof contexts.

#. Constraints:

   * No further Global-specific requirements needed.

#. Consistency:

   * **Requirement:** The mode associated with a formal parameter [of an enclosing subprogram]
     or volatile variable in a global data list
     shall be consistent with the mode associated with it at the point of its declaration.
     
     **Rationale:** this provides an early basic consistency check.

#. Semantics: 

   * **Requirement:** A global data item with an input mode is read on at least one
     executable path.

     **Rationale:** by definition.

   * **Requirement:** A global data item with an output mode is written on at least one
     executable path.
 
     **Rationale:** by definition.

   * **Requirement:** A global data item with an output mode but no input mode is written
     on all executable paths.

     **Rationale:** to ensure that data items with output mode are always initialized
     on completion of a call to the subprogram.

   * **Requirement:** A global data item that is only read in a proof context shall not have
     an input or output mode.

     **Rationale:** the effect of reading data items in a proof context is fundamentally
     different from the reading of data items outside of a proof context, since the
     former does not contribute to information flow relations.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Depends Aspects
~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify the dependency relation - that is, which outputs
     are dependent on which inputs - that is met by a given subprogram.

     **Rationale:** To allow provision of at least the same functionality as SPARK 2005
     and to allow modular analysis.

   * **Requirement:** It shall be possible to refer to both global data and formal parameters
     in the dependency relation.

     **Rationale:** The inputs and outputs are given by both the global data and the
     formal parameters.

   * **Requirement:** It shall be possible to assume an implicit dependency relation on functions
     and so an explicit statement shall not be required.

     **Rationale:** this is typical usage and saves effort.

#. Constraints:

   * No further Depends-specific requirements needed.

#. Semantics: 

   * **Requirement:** That (X,Y) is in the dependency relation for a given subprogram
     (i.e. X depends on Y) means that X is an output of the subprogram
     such that the entry value of the input Y is used to set the exit value of X on
     at least one executable path.

     **Rationale:** by definition.

#. Consistency:

    * **Requirement:** The dependency relation defines an alternative view of the inputs and outputs
      of the subprogram and that view must be equivalent to the list of global
      data items and formal parameters and their modes (ignoring data items used only in proof contexts).

      **Rationale:** this provides a useful early consistency check.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Ghost Functions
~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** It shall be possible to specify functions which are used
     for testing and verification only.  Their presence should have no effect on
     the functionality of program execution which terminates normally 
     (without exception).

     **Rationale:**   In principle such functions could be removed from the
     code (possibly automatically by the compiler) on completion of testing 
     and verification and have no effect on the functionality of the program.

   * **Requirement:** It shall be possible to specify functions which are used
     for formal verification only which have no implementation.

     **Rationale:** A function used for formal verification purposes may be
     difficult (or impossible) to specify or implement in |SPARK|. A function
     without an implementation will be defined, for proof purposes, in an 
     external proof tool.

#. Constraints:

   * In order to be removed they can only be applied in places where it can be
     ascertained that they will not be called during normal execution of the
     program (that is with test and verification constructs disabled).
    
   * A function without an implementation cannot be called during execution of
     a program.

#. Consistency:

   Not applicable.

#. Semantics: 

   Not applicable.

#. General requirements:

    * See also section :ref:`ghost_entities`.

Subprogram Calls
----------------

Anti-Aliasing
~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * Not applicable.

#. Constraints:

   * **Requirement:** An entity that may be updated on a call to a subprogram
     may not be referred to by distinct names within that subprogram.

     **Rationale:** Flow analysis specifications are presented and analyzed in
     terms of names rather than the entities to which those names refer.

#. Semantics: 

   * Not applicable.

#. Consistency:

    * Not applicable.

#. General requirements:

    * Not applicable.

Packages
========

Package Specifications and Declarations
---------------------------------------

Abstract State Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible to provide an abstracted view of hidden state that can be referred to
      in specifications of program behavior.

      **Rationale:** this allows modular analysis, since modular analysis is performed
      before all package bodies are available and so before all hidden state is known.
      Abstraction also allows the management of complexity.

#. Constraints:

   * No further abstract state-specific requirements.

#. Consistency:

    * No further abstract state-specific requirements.

#. Semantics:

    * No further abstract state-specific requirements.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Initializes Aspect
~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** Flow analysis requires the knowledge of whether each
      variable has been initialized.  It should be possible to determine this
      from the specification of a unit.

      **Rationale:** Variables and state abstractions may be initialized within
      a package body as well as a package specification.  It follows not all
      initializations are visible from the specification.  An Initializes aspect
      is applied to a package specification to indicate which variables and
      state abstractions are initialized by the package.  This facilitates
      modular analysis.
      
#. Constraints:

   * No further Initializes-specific requirements.

#. Consistency:

    * No further Initializes-specific requirements.

#. Semantics:

    * **Requirement:** The set of data items listed in an Initializes aspect shall be fully initialized
      during elaboration of this package.

      **Rationale:** To ensure that listed data items are always initialized before use.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Initial Condition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible to formally specify the result of performing package elaboration.

      **Rationale:** This specification behaves as a postcondition for the result of package elaboration
      and so establishes the "pre-condition" that holds at the point of beginning execution of the program proper.
      Giving an explicit postcondition supports modular analysis.

#. Constraints:

   * No further Initial Condition-specific requirements.

#. Consistency:

    * No further Initial Condition-specific requirements.

#. Semantics:

    * **Requirement:** The predicate given by the Initial Condition aspect should evaluate to
      True at the point at which elaboration of the package, its embedded packages and its private descendants has completed.

      **Rationale:** By definition.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Package Bodies
--------------

.. _refinement-rationale:

Common Rationale for Refined Aspects
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Where it is possible to specify subprogram behavior using a language feature that
refers to abstract state, it should be possible to define a corresponding *refined*
version of the language feature that refers to the decomposition of that abstract state.

The rationale for this is as follows:

#. The semantics of properties defined in terms of abstract state
   can only be precisely defined in terms of the corresponding concrete state,
   though nested abstraction is also necessary to manage hierarchies of data.

#. There may be multiple possible refinements for a given abstract specification
   and so the user should be able to specify what they actually want.

#. This is necessary to support development via stepwise refinement.


Refined State Aspect
~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** For each state abstraction, it shall be possible to define the set of hidden
     state items that implement or *refine* that abstract state (where the
     hidden state items can either be concrete state or further state abstractions).
     
     **Rationale**: see section :ref:`refinement-rationale`.

#. Constraints:

   * **Requirement:** Each item of hidden state must map to exactly one state abstraction.

     **Rationale:** all hidden state must be covered since otherwise specifications referring to abstract state may
     be incomplete; each item of that hidden state must map to exactly one abstraction to give a clean and easily understandable
     abstraction, and for the purposes of simplicity of analysis.

   * **Requirement:** Each item of abstract state covered by the package shall be mapped to at least one
     item of hidden state (either concrete state or a further state abstraction).

     **Rationale:** the semantics of properties defined in terms of abstract state
     can only be precisely defined in terms of the corresponding concrete state.

   * **Requirement:** Each item of hidden state should appear in at least one global data list
     within the package body.

     **Rationale:** If this is not the case, then there is at least one hidden state item that is not
     used by any subprogram.

#. Consistency:

   * No further Refined state-specific requirements needed.

#. Semantics:

   * No further Refined state-specific requirements needed.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Refined Global Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a global data list referring to abstract state has been specified for a subprogram,
     it shall be possible to provide a refined global data list that takes account of the
     refinement of that abstract state.

     **Rationale:** see section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined Global-specific requirements needed.

#. Consistency:

   * Let *Abstract* be the abstraction function defined by state refinement (such that
     *Abstract* is the identity function when applied to visible state).
     Let *G* be the global data list and *RG* be the refined global data list. Then:

     * **Requirement:** If *X* appears in *RG* but not all constituents of *Abstract (X)* appear in *RG*
       then *Abstract (X)* must appear in *G* with at least input mode.

       **Rationale:** In this case, *Abstract (X)* is not fully initialized by the
       subprogram and the relevant components must be intialized prior to calling
       the subprogram.

     * **Requirement:** If *Y* appears in *G*, then at least one *X* such that *Abstract (X) = Y*
       must appear in *RG*.

       **Rationale:** By definition of abstraction.
     
     * **Requirement:** Refinement of modes:

          * If the mode of *X* in *RG* indicates it is **not** used in a
            proof context, then that mode must be a mode of *Abstract (X)* in *G*.

          * If the mode of *X* in *RG* indicates it **is** used in a proof context and
            *Abstract(X)* does not have another mode according to the above rules, then the
            mode of *Abstract(X)* shall indicate it is only used in proof contexts.

       **Rationale:** In general, modes should be preserved by refinement. However,
       if one refinement constituent of a state abstraction has an input and/or output mode, then
       it is no longer of interest whether another constituent is only used in a
       proof context.

#. Semantics:

   * As per Global aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Refined Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a dependency relation referring to abstract state has been given,
     it shall be possible to specify a refined dependency relation that takes account
     of the refinement of that abstract state.

     **Rationale:** see section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined depends-specific requirements needed.

#. Consistency: 

    * **Requirement:** The refined dependency relation defines an alternative view of the inputs and outputs
      of the subprogram and that view must be equivalent to the refined list of global
      data items and formal parameters and their modes (ignoring data items used only in proof contexts).

      **Rationale:** this provides a useful early consistency check.


    * Let *Abstract* be the abstraction function defined by state refinement (such that
      *Abstract* is the identity function when applied to visible state).
      Let *D* be a dependency relation and *RD* be the corresponding
      refined dependency relation. Then:

      * **Requirement:** If *(X,Y)* is in *RD* - i.e. *X* depends on *Y* -
        then *(Abstract(X), Abstract(Y))* is in *D*.

        **Rationale:** dependencies must be preserved after abstraction.

      * **Requirement:** If *(X,Y)* is in *RD* and there is *A* such that *Abstract(A)=Abstract(X)* but
        there is no *B* such that *(A,B)* is in *RD*, then *(Abstract(X),Abstract(X))* is in *D*.

        **Rationale:** In this case, *Abstract (X)* is not fully initialized by the
        subprogram and the relevant components must be initialized prior to calling
        the subprogram.

      * **Requirement:** If *(S,T)* is in *D* then there shall exist *(V,W)* in *RD* such that
        *Abstract(V)=S* and *Abstract(W)=T*.

        **Rationale:** By definition of abstraction.

#. Semantics:

   * As per Depends aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Refined Precondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a precondition has been provided for a subprogram declaration, it shall be
     possible to state a refined precondition that refers to concrete rather than abstract state
     and/or concrete rather than abstract type detail.

     **Rationale:** See section :ref:`refinement-rationale`.

#. Constraints:

   * No further Refined precondition-specific requirements needed.

#. Consistency: 

   * **Requirement:** The refined precondition of the subprogram must be implied by the precondition.

     **Rationale:** standard definition of proof refinement.

#. Semantics:

   * As per the semantics of the Precondition aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Refined Postcondition Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** Where a post-condition has been provided for a subprogram declaration, it shall be
     possible to state a refined post-condition that refers to concrete rather than abstract state
     and/or concrete rather than abstract type detail.

     **Rationale:** See section :ref:`refinement-rationale`.   

#. Constraints:

   * No further Refined post-condition-specific requirements needed.

#. Consistency: 

   * **Requirement:** The post-condition of the subprogram must be implied by the refined post-condition.

     **Rationale:** standard definition of proof refinement.

#. Semantics:

   * As per the semantics of the Post-condition aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

Visibility Rules
================

Tasks and Synchronization
=========================

Program Structure and Compilation Issues
========================================

**High-Level Requirements**


#. Goals to be met by language feature:

   * **Requirement:** The ability to analyze incomplete programs.

     **Rationale:** In order to support incremental development and analysis.
     To facilitate the use of flow analysis and formal verification as early as
     possible in the software life-cycle.

#. Constraints, Consistency, Semantics, General requirements:

   * Interface specifications have to be provided for all modules.  In analysis
     the module is represented by its interface specification.

Separate Compilation
--------------------

Context Clauses - With Clauses
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

High-Level Requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

   * **Requirement:** State abstractions and visible variable declarations shall
     be visible in the limited view of a package.

     **Rationale:** This allows the flow analysis specifications of a package P1
     to refer to the state of P2 in the case that P1 only has a limited
     view of P2.

#. Constraints, Consistency, Semantics, General requirements:

   * Not applicable.

Exceptions
==========

High-Level Requirements
-----------------------

#. Goals to be met by language feature:

   * Not applicable.

#. Constraints:

   * **Requirement:** Most explicit uses of exceptions are excluded from |SPARK| as described below.
     Exceptions can be raised implicitly (for example, by the failure of a language-defined check),
     but only in the case of a program with an undischarged (or incorrectly discharged, perhaps via an incorrect
     Assume pragma) proof obligation. Explicit raising of exceptions is dealt with similarly.

     **Rationale:** Raising and handling of exceptions allow forms of control flow that complicate
     both specification and verification of a program's behavior.

#. Consistency:

   * Not applicable.

#. Semantics:

   * Not applicable.

#. General requirements:

    * Not applicable.
