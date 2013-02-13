Packages
========

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
~~~~~~~~~~~~~~~~~~~~

The variables declared immediately within a package Q, its embedded
packages and its private descendants constitute the state of Q.

The variable declarations are only visible to clients of Q if they
are declared in the ``visible_part`` of Q.  The
declarations of all other variables are *hidden* from a client of Q.
Though the variables are hidden they still form part (or all) of the
state of Q and this hidden state cannot be ignored for static analyses
and proof.  *State abstraction* is the means by which this hidden state
is managed for static analyses and proof.

|SPARK| extends the concept of state abstraction to provide
hierarchical data abstraction whereby the hidden state of a package Q
may be refined over a tree of private descendants or embedded packages
of Q.  This provides data refinement similar to the refinement
available to types whereby a record may contain fields which are
themselves records.

State abstraction supports a logical model of volatility.  A *volatile*
state does not behave like a standard non-volatile one as its value
may change between two successive reads without an intervening update,
or successive updates may occur without any intervening reads and
appear to have no effect on the program.  Often volatile states
represent inputs or outputs to external devices or subsystems. *Note, however,
that the current draft does not include a complete model of volatile state.*

The abstract state aspect provides a way to designate a named abstract state as
being volatile, usually representing an external input or output.

.. _abstract-state-aspect:

Abstract State Aspect
~~~~~~~~~~~~~~~~~~~~~

High-level requirements
^^^^^^^^^^^^^^^^^^^^^^^

#. Goals to be met by language feature:

    * **Requirement:** It shall be possible to provide an abstracted view of hidden state that can be referred to
      in specifications of program behavior.

      **Rationale:** this allows modular analysis, since modular is analysis performed
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


Language definition
^^^^^^^^^^^^^^^^^^^

State abstraction provides a mechanism for naming, in a package's
``visible_part``, state (typically variable declarations) that will be
declared within the package's body (or ``private_part``, or within private
descendants of the package). For example, a package declares a visible
procedure and we wish to specify the set of global variables that the
procedure reads and writes as part of the specification of the
subprogram. Those variables cannot be named directly in the package
specification. Instead, we introduce a state abstraction which is
visible in the package specification and later, when the package body
is declared, we specify the set of variables that *constitute* or
*implement* that state abstraction. If a package body contains, for
example, a nested package, then a state abstraction of the inner
package may also be part of the implementation of the given state
abstraction of the outer package.

The *hidden* state of a package may be represented
by one or more state abstractions, with each pair of state
abstractions representing disjoint sets of hidden variables.

If a subprogram P with a Global Aspect is declared in the
``visible_part`` of a package and P reads or updates any of the hidden
state of the package then P must include in its Global Aspect the
abstract state names with the correct mode that represent the hidden
state referenced by P.  If P has a Depends aspect then the abstract
state names must appear as inputs and outputs of P, as appropriate, in
the ``dependency_relation`` of the Depends aspect.

The Abstract State Aspect is introduced by an ``aspect_specification``
where the ``aspect_mark`` is Abstract_State and the
``aspect_definition`` must follow the grammar of
``abstract_state_list`` given below.

.. centered:: **Syntax**

::

  abstract_state_list        ::= null
                               | state_name_with_properties
                               | (state_name_with_properties { , state_name_with_properties } )
  state_name_with_properties ::= state_name
                               | ( state_name with property_list )
  property_list              ::= property { , property }
  property                   ::= simple_property
                               | name_value_property
  simple_property            ::= identifier
  name_value_property        ::= identifier => expression
  state_name                 ::= defining_identifier

.. ifconfig:: Display_Trace_Units

   :Trace Unit: 7.1.2 Syntax

.. centered:: **Legality Rules**

#. The ``identifier`` of a ``simple_property`` shall be Volatile,
   Input, or Output.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR identifier of simple_property shall be Volatile, Input or Output

#. There shall be at most one occurrence of the ``identifiers``
   Volatile, Input and Output in a single ``property_list``.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR At most one occurrence of Volatile, Input and Output in single property_list

#. If a ``property_list`` includes Volatile, then it shall also
   include exactly one of Input or Output.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list includes Volatile, then it shall also include exactly one of Input or Output

#. If a ``property_list`` includes either Input or Output,
   then it shall also include Volatile.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list includes Input or Output, it shall also include Volatile

#. The ``identifier`` of a ``name_value_property`` shall be
   Integrity.

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR name_value_property identifier must be Integrity

#. If a ``property_list`` includes Integrity then it shall be the final
   property in the list. [This eliminates the possibility of a positional
   association following a named association in the property list.]

   .. ifconfig:: Display_Trace_Units

      :Trace Unit: 7.1.2 LR If property_list has Integrity it must be the final property in the list

#. A package_declaration or generic_package_declaration requires a completion
   [(a body)] if it contains a non-null Abstract State aspect specification.

.. centered:: **Static Semantics**

#. The visible state and state abstractions of a package P consist of:

   * any variables declared immediately within the visible part
     of P; and
   * any state abstractions declared by the Abstract State aspect
     specification (if any) of package P; and
   * the visible state and state abstractions of any packages declared
     immediately within the visible part of P.

#. The hidden state of a package P consists of:

   * any variables declared immediately within the private part or
     body of P; and
   * the visible state and state abstractions of any packages declared
     immediately within the private part or body of P, and of any
     private child units of P or of their public descendants.

.. note::
 (SB) These definitions may eventually be expanded to include non-static
 constants, not just variables.

#. Each ``state_name`` occurring in an Abstract_State aspect
   specification for a given package P introduces an implicit
   declaration of a *state abstraction* entity. This implicit
   declaration occurs at the beginning of the visible part of P. This
   implicit declaration requires completion and is overloadable.

.. note::
 (SB) Making these implicit declarations overloadable allows declaring
 a subprogram with the same fully qualified name as a state abstraction;
 to make this scenario work, rules of the form "... shall denote a state
 abstraction" need to be name resolution rules, not just legality rules.

#. [A state abstraction shall only be named in contexts where this is
   explicitly permitted (e.g., as part of a Globals aspect
   specification), but this is not a name resolution rule.  Thus, the
   declaration of a state abstraction has the same visibility as any
   other declaration.
   A state abstraction is not an object; it does not have a type.  The
   completion of a state abstraction declared in a package
   aspect_specification can only be provided as part of a
   Refined_State aspect specification within the body of the package.]
   
#. A **null** ``abstract_state_list`` specifies that a package contains no 
   hidden state or variables declared in its ``visible_part``.
   [The specification is is checked when the package is analyzed.]

#. A *volatile* state abstraction is one declared with a property list
   which includes the Volatile property, and either Input or Output.

.. centered:: **Verification Rules**

There are no Verification Rules associated with the Abstract State aspect.
   
.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the Abstract State
aspect.

.. centered:: **Examples**

.. code-block:: ada

   package Q
   with
      Abstract_State => State           -- Declaration of abstract state name State
   is                                   -- representing internal state of Q.
     function Is_Ready return Boolean   -- Function checking some property of the State.
        with Global => State;           -- State may be used in a global aspect.

        procedure Init                    -- Procedure to initialize the internal state of Q.
        with Global => (Output => State), -- State may be used in a global aspect.
	     Post   => Is_Ready;

        procedure Op_1 (V : Integer)    -- Another procedure providing some operation on State
           with Global => (In_Out => State),
  	        Pre    => Is_Ready,
	        Post   => Is_Ready;
   end Q;

   package X
      with  Abstract_State => (A, B, (C with Volatile, Input))
   is                          -- Three abstract state names are declared A, B & C.
                               -- A and B are non-volatile abstract states
      ...                      -- C is designated as a volatile input.
   end X;

   package Sensor -- simple volatile, input device driver
      with Abstract_State => (Port with Volatile, Input);
   is
      ...
   end Sensor;

.. todo: Further semantic detail regarding Volatile state and integrity levels
         needs to be added, in particular in relation to specifying these
         properties for variables which are declared directly within the
         visible part of a package specification.


Package-level Global, Depends and Initializes
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
**High-level detail TBD.**

For analysis purposes, the elaboration of a 
package is considered as a call of a set of nested subprograms.  
For instance, the elaboration of the package specification is the external client
view of the elaboration, but the elaboration of the specification notionally
calls the elaboration of any packages on which it depends and the elaboration
of the package body.  The elaboration of the package body calls the elaboration
of any packages on which it depends and so forth.  This model does not address
the issue of incorrect elaboration order or elaboration order circularities but 
these will be dealt with elsewhere.

The net result of this view of package elaboration is that every package which
contains some form of state has a Global and a Dependency aspect representing
the composite view of the nested subprogram calls at the level of abstraction 
presented by the package specification.  

.. note::
 (SB) In the case of whole-program analysis which includes analysis of the
 elaboration code for a partition (loosely speaking, for a main program).
 we want to treat a (binder-generated, at least in the GNAT implementation)
 call to an elaboration subprogram just like any other subprogram call. This
 means that the elaboration routine for, for example, a library unit package
 spec or body must have the same aspects defined as any other procedure:
 Global, Depends, Pre and Post (although giving these aspects different
 names in the case of elaboration routines would be acceptable). [The
 no-longer-defined Initial_Condition aspect of a package
 roughly corresponded to the postcondition of package body's elaboration,
 although it was confusingly conflated with private descendant units.] For
 purposes of precisely analyzing elaboration code, we do not
 want to lump together spec elaboration, body elaboration, and the spec
 and body elaboration of private descendants. It is possible that we
 might want to do something less precise (along the lines of the
 "notionally calls" idea mentioned above) only in the "modular" (as opposed to
 "whole program") case where the program's elaboration order is only
 partially known. It is not clear yet whether this "notionally calls"
 approach is a useful idea; TBD.

.. centered:: **Legality Rules**

#. The package Global and Depends aspects may only appear in the 
   ``aspect_specification`` of a ``package_specification``.


Global Aspects
~~~~~~~~~~~~~~

**High-level detail TBD.**

The syntax and semantics for a package Global aspect is the same as for a 
subprogram Global aspect when one considers the package elaboration as a 
subprogramaspect :ref:`global-aspects`.  

Initializes Aspects
~~~~~~~~~~~~~~~~~~~

Very often a package will have no dependencies but only initialize its own 
state, that is variables declared in the package or in its private descendants.
In such cases an Initializes aspect may be used rather than a Global aspect.

The Initializes aspect is introduced by an ``aspect_specification`` where the 
``aspect_mark`` is Initializes and the ``aspect_definition`` must follow the 
grammar of ``initialization_list`` given below.

.. centered:: **Syntax**

::

  initialization_list ::= global_list
  
An initialization list is shorthand for a Global aspect of the form

::
   
  Global => (Output => global_list)
   
where the ``global_items`` denoted in the ``global_list`` are identical, each 
is a variable or state abstraction and declared within the ``visible_part`` 
of the package containing the Initializes aspect.


Package Bodies
--------------

State Refinement
~~~~~~~~~~~~~~~~

A ``state_name`` declared by an Abstract State Aspect in the
specification of a package Q is an abstraction of the non-visible
variables declared in the private part, body, or private descendants
of Q, which together form the hidden state, of Q.  In the body of Q
each ``state_name`` has to be refined by showing which variables and
subordinate abstract states are represented by the ``state_name`` (its
constituents).  A Refined State Aspect in the body of Q is used
for this purpose.

In the body of a package the constituents of the refined
``state_name``, the refined view, has to be used rather than the
abstract view of the ``state_name``.  Refined global, depends, pre
and post aspects are provided to express the refined view.

In the refined view the constituents of each ``state_name`` have to be
initialized consistently with their appearance or omission from the
Package Depends or Initializes aspect of the package.

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


.. todo:: The consistency rules will be updated as the
          models for volatile variables and integrity levels are defined.

.. todo: Consider whether it should be possible to refine null abstract state onto hidden state.
     *Rationale: this would allow the modeling of programs that - for example - use caches
     to improve performance.*

.. todo:: Consider whether it should be possible to refine abstract onto hidden state without any restrictions,
     although the refinement would be checked and potential issues flagged up to the user.
     
     **Rationale:** there are a number of different possible models of mapping abstract
     to concrete state - especially when volatile state is being used - and it might
     be useful to provide greater flexibility to the user. In addition, if a facility is
     provided to allow users to step outside of the language when refining depends, for example, then it may be
     necessary to relax the abstraction model as well as relaxing the language feature
     of direct relevance.*


Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 3 version of this document.*


Abstract State and Package Hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. todo:: We need to consider the interactions between package hierarchy and abstract state.
   Do we need to have rules restricting access between parent and child packages?
   Can we ensure abstract state encapsulation? Target: D2.

Volatile Variables
~~~~~~~~~~~~~~~~~~

A volatile ``state_name`` may be refined to one or more subordinate
``state_names`` but ultimately a volatile ``state_name`` has to be
refined on to one or more volatile *variables*.  This variable has to
be volatile. The volatile *variable* will be declared in the body of a
package and the declaration will normally be denoted as volatile using
an aspect or a pragma.  Usually it will also have a representation
giving its address.

A volatile variable cannot be mentioned directly in a contract as the
reading of a volatile variable may affect the value of the variable
and for many I/O ports a read and a write affect different registers
of the external device.

.. todo:: Rather than have the current problems with external
   variables in functions should we disallow them in functions?
   Perhaps wait for a more general solution which allows non-pure
   functions in certain situations.

   We need to consider a way of providing features for reasoning about
   external variables different to the broken 'Tail scheme in SPARK 2005.
   This will require some form of attribute as we cannot mention
   volatile variables directly in a contract.

   If we want to reason about successive reads (writes) from a Volatile
   Input (Output) ``state_name`` we need to have a way to refer to
   these individual operations.

   At the very least, if V is a Volatile Input variable should not
   have the following assertion provable:

   T1 := V;
   T2 := V;

   pragma Assert (T1 = T2);

   Target: D2.

.. todo:: May introduce a way to provide a "history" parameter for
   Volatile variables. Target: D2.

.. todo:: Consider a mode selector for the "latched output" pattern - one that can be
   read after writing but need not be. This scheme has been
   requested by secunet.  In this scheme the output would be volatile
   but the input non-volatile. Target: rel2+.


Initialization Refinement
~~~~~~~~~~~~~~~~~~~~~~~~~

**High-level detail TBD.**


.. _refined-global-aspect:

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
            *Abstract(X)* will not have another mode according to the above rules, then the
            mode of *Abstract(X)* shall indicate it is only used in proof contexts.

       **Rationale:** In general, modes should be preserved by refinement. However,
       if one refinement constituent of a state abstraction has an input and/or output mode, then
       it is no longer of interest whether another constituent is only used in a
       proof context.

#. Semantics:

   * As per Global aspect.

#. General requirements:

    * See also section :ref:`generic_hlrs`.

.. todo:: The consistency rules will be updated as the
          model for volatile variables is defined.

.. todo: If it ends up being possible to refine null abstract state, then refinements of such
         state could appear in refined globals statements, though they would need
         to have mode in out.

Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 3 version of this document.*


.. _refined-depends-aspect:

Refined Depends Aspect
~~~~~~~~~~~~~~~~~~~~~~~~~

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

.. todo:: The consistency rules will be updated as the
          model for volatile variables is defined.

.. todo: If it is possible to refine null abstract state, then refinements of such
         state could appear in refined depends statements, but wouldn't map to
         anything in the depends relation itself and would need to have mode in/out
         in the refined depends.

Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 3 version of this document.*


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

Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 3 version of this document.*

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

Language Definition
^^^^^^^^^^^^^^^^^^^

*To be completed in the Milestone 3 version of this document.*

.. todo:: refined contract_cases. Target: D2.


Private Types and Private Extensions
------------------------------------

.. centered:: **Extended Static Semantics**

#. The partial view of a private type or private extension may be in
   |SPARK| even if its full view is not in |SPARK|. The usual rule
   applies here, so a private type without discriminants is in
   |SPARK|, while a private type with discriminants is in |SPARK| only
   if its discriminants are in |SPARK|.

Private Operations
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Type Invariants
~~~~~~~~~~~~~~~

.. centered:: **Syntax**

There is no additional syntax associated with type invariants.

.. centered:: **Legality Rules**

There are no additional legality rules associated with type invariants.

.. centered:: **Static Semantics**

There are no additional static semantics associated with type invariants.

.. centered:: **Dynamic Semantics**

There are no additional dynamic semantics associated with type invariants.

.. centered:: **Verification Rules**

#. The Ada 2012 RM lists places at which an invariant check is performed. In
   |SPARK|, we add the following places in order to guarantee that an instance
   of a type always respects its invariant at the point at which it is passed
   as an input parameter:

   * Before a call on any subprogram or entry that:

     * is explicitly declared within the immediate scope of type T (or
       by an instance of a generic unit, and the generic is declared
       within the immediate scope of type T), and

     * is visible outside the immediate scope of type T or overrides
       an operation that is visible outside the immediate scope of T,
       and

     * has one or more in out or in parameters with a part of type T.

     the check is performed on each such part of type T.
     [Note that these checks are only performed statically, and this does not create an
     obligation to extend the run-time checks performed in relation to type invariants.]

Deferred Constants
------------------

.. todo:: Need to consider here allowing a Global Aspect on a deferred
   constant declaration to indicate the variables from which the
   value is derived.  Will be needed if the completion is not in |SPARK|, for instance.
   Target: D2.

Limited Types
-------------

No extensions or restrictions.

Assignment and Finalization
---------------------------

Controlled types are not permitted in |SPARK|.
