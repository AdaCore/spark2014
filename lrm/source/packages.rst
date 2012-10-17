Packages
========

Package Specifications and Declarations
---------------------------------------

.. _abstract-state:

Abstraction of State
^^^^^^^^^^^^^^^^^^^^

The *variables* declared in a package Q, embedded packages declared
within Q, and the private children of Q constitute the state of a
package.  The *variable* declarations are only visible to users of Q
if they are declared in the ``visible_part`` of Q which is not good
practice.  The declarations of all other variables are hidden from the
user of Q.  Though the variables are hidden they still form part (or
all) of the state of Q and this state cannot be ignored for static
analyses and proof.


Abstract State Aspect
^^^^^^^^^^^^^^^^^^^^^

An abstract state is a name representing the state embodied by the
hidden *variables* of a package. The overall state of a package may be
represented by one or more visible *variables* and abstract states.
An abstract state of a package has no type and may only be used within
a ``global_aspect`` or a ``dependency_aspect`` or their refined
counterparts.

If a subprogram P with a ``global_aspect`` is declared in the
``visible_part`` of a package and P reads or updates any of the hidden
*variables* of the package then P must include in its
``global_aspect`` the abstract states with the correct mode that
represents the hidden *variables* referenced by P.  If P has a
``dependency_aspect`` then the abstract states must appear as imports
and exports, as appropriate, in the ``dependency_relation`` of the
aspect.


.. centered:: **Syntax**

::

  abstract_state_aspect ::= Abstract_State => abstract_state_list
  abstract_state_list   ::= state_name
                          | (state_name {, state_name})
  state_name            ::= defining_identifier [=> (Volatile => mode_selector)]

.. todo:: May be we have to consider a latched output mode selector,
   one that can be read after writing but need not be.  This scheme
   has beeen requested by secunet.

.. centered:: **Legality Rules**

#. An ``abstract_state_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. At most one ``abstract_state_aspect`` may appear in a single
   ``aspect_specification``.
#. The ``defining_identifier`` of a ``state_name`` must not be the
   same as a directly visible name or a name declared immediately
   within the package containing the ``abstract_state_aspect``.
#. The ``defining_identifier`` of a ``state_name`` shall not be
   repeated within the ``abstract_state_list``.
#. A ``state_name`` can only appear in a ``initializes_aspect``, a
   ``global_aspect``, a ``dependency_aspect``, their refinded
   counterparts, or their equivalent pragmas.
#. The Volatile designates a volatile state, usually an external
   input or output.  The mode selector determines whether the volatile
   state is an input or an output or possibly both an input and an
   output (an in_out).
#. A volatile state may have the attributes ``Head``, ``Tail``.
#. A volatile input may be an ``import`` only.
#. A volatile output may be an ``export`` only.
#. A volatile in_out has the attributes ``Input`` and ``Output``.
#. A volatile in_out ``state_name`` cannot be used directly it must be
   attributed with ``Input`` or ``Output``
#. A volatile in_out ``state_name`` S may be used as an ``import``
   using the notation S'Input and used as an export using the notation
   S'Output.

.. centered:: **Static Semantics**

#. An abstract ``state_name`` is declared using a
   ``abstract_state_aspect`` appearing in an ``aspect_specification``
   of a ``package_specification``.
#. A ``state_name`` has the same scope and visibility as a declaration
   in the ``visible part`` of the package to which the
   ``abstract_state_aspect`` is applied.
#. An abstract state of a package is generally considered to be in one
   of the following categories:
 
   * Unititalized State - state which is not initialized during the
     package elaboration
   * Initialized State - state which is initialized during the package
     elaboration
   * Volatile Input State - Volatile state which is an input only.
     Volatile Input State is considered to be implicitly initialized
   * Volatile Output State - Volatile state which is an output only.
     Volatile Output State is considered to be implicitly initialized
   * Volatile In_Out State - Volatile state which is bidirectional.
     Volatile In_Out State is considered to be implicitly initialized

#. A volatile state is considered to be a sequence of values, a
   volatile In_Out state has two sequences, an input and and an output
   sequence.  The input sequence is denoted using the ``Input``
   attribute and the output sequence is denoted by the ``Output``
   attribute.
#. Each time an input or in_out state is read (indirectly through its
   refinement) its value may be different.  This distinction with a
   normal non-volatile variable or state is important for both flow
   analysis and proof.
#. A volatile output or in_out state may be updated many times but
   each individual update is considered to have an effect.  This is in
   contrast with a normal non-valatile variable or state where
   successive updates with no interniving reads would indicate that
   earlier updtaes were ineffective.  Flow analysis and proof have to
   take account of this difference.
#. If a package has internal state but no ``abstract_state_aspect`` is
   provided, an implicit ``state_name`` is generated for each category
   of abstract state.  The implicit ``state_names`` cannot be
   referenced directly but they may be indirectly accessed using the
   following attributes for the different categories of abstract
   state:

   * *package_*\ ``name'Uninitialized_State``
   * *package_*\ ``name'Initialized_State``
   * *package_*\ ``name'Volatile_Input_State``
   * *package_*\ ``name'Volatile_Output_State``
   * *package_*\ ``name'Volatile_In_Out_State``


.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.2 Abstract State Aspect
   :end-before: 7.1.3 

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``abstract_state_aspect`` the rules are checked by static analysis.


Initializes Aspect
^^^^^^^^^^^^^^^^^^

An important property of the state components of a package is whether
they are initialized during package elaboration.  Flow analysis
determines that the program state has been initialized and the
``initializes_aspect`` provides this information without having to
analyse the body of the package if it exists.

.. centered:: **Syntax**

::

  initializes_aspect    ::= Initializes => initialized_item_list
  initialized_item_list ::= initialized_item
                          | (initialized_item {, initialized_item})


where

   ``initialized_item  ::= state_name |`` *variable_*\ ``name``


.. centered:: **Legality Rules**

#. An ``initializes_aspect`` may only appear in the
   ``aspect_specification`` of a package specification.  
#. There can be at most one ``initializes_aspect`` in an
   ``aspect_specification``.
#. An ``initialized_item`` is either:

   * a ``state_name`` declared in a previous ``abstract_state_aspect``
     within the same ``aspect_specification``; or
   * the name of a *variable* declared in the visible part of the
     package specification which contains the ``initializes_aspect``.

#. A *variable* appearing in an ``initializes_aspect`` must be entire,
   it cannot be a subcomponent of a containing object.
#. An ``initialized_item`` may not appear more than once in an
   ``initialized_item_list``.
#. A ``state_name`` which is designated as ``Volatile`` must not
   appear in an initializes aspect.

.. centered:: **Static Semantics**

#. An ``initialized_item`` appearing in a ``initializes_aspect``
   indicates that it is initialized during package elaboration.
#. The absence of a ``state_name`` of a package Q or a *variable*
   declared in the visible part of Q in the ``ininializes_aspect`` of
   Q indicates that the ``state_name`` or *variable* is not
   initialized during package elaboration.
#. A ``state_name`` designated as ``Volatile`` is considered to be
   implicitly initialized.
#. If a package has an ``abstract_state_aspect`` but no
   ``initializes_aspect`` it follows that none of its state components
   are initialized during the package initialization.

.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.3 Initializes Aspect
   :end-before: 7.1.4

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``initializes_aspect`` the rules are checked by static analysis.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. If a package has an ``initializes_aspect`` and it has non-visible
   state components, it must be preceded by an
   ``abstract_state_aspect`` in the same ``aspect_specification``.
#. Each *variable* appearing in an ``initializes_aspect`` of a package
   Q must be initialized either at the point of declaration in Q or
   within the sequence of statements of the body of Q.
#. Each ``constituent`` of a ``state_name`` declared in a package Q
   that is a *variable* must be initialized at its point of
   declaration within Q, or if it is a *variable* declared in the
   visible part of a private child or embedded package package of Q,
   then it must appear in the ``initializes_aspect`` of the private
   child or embedded package.
#. Each ``constituent`` of a ``state_name`` which is a ``state_name``
   of a private child or embedded package must appear in the
   ``initializes_aspect`` of the private child or embedded package.
#. If a package Q has an ``initializes_aspect`` and it does not a
   contain a *variable* or ``state_name`` V, then neither V nor its
   constituents, if it is a ``state_name``, should be initialized
   during the elaboration of Q, its private child or its embedded
   packages.
#. If a package has neither an ``abstract_state_aspect`` nor an
   ``initializes_aspect`` but it has state components, then analysis
   of the package specification and body (if it exists) will determine
   the *varibles* declared in the package and whether they are
   initialized during elaboration of the package.  For *variables* not
   declared in the visible part of the package an implicit
   ``state_name`` is generated to represent the *variables* which are
   not initialized and another for the *variables* which are
   initialized. The ``state_name`` representing the initialized
   *variables* is added to an implicitly generated
   ``initialization_aspect`` along with any *variables* which are
   declared in the visible part of the package wich are initialized
   during package elaboration.

.. todo:: Note that I do not think we can automatically determine volatile variables.

Initial Condition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^

The ''initial_condition_aspect`` is a prdeicate that may be used to
describe formally the state of a package.  It behaves as a
postcondition for the package initialization.

.. centered:: **Syntax**
  
``initial_condition_aspect ::= Initial_Condition =>`` *Boolean_*\ ``expression``


 .. centered:: **Legality Rules**

#. An ``initial_condition_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. At most one ``initial_condition_aspect`` may appear in a single
   ``aspect_specification``.
#. The expression of an ``initial_condition_aspect`` has extended
   vsibility.  It may reference declarations from the visible part of
   Q.
#. Each *variable* declared in the visible part of a package Q and
   appearing in the ``initial_condition_aspect`` of Q must be
   initialized during the elaboration of Q.
#. Each ``state_name`` declared package Q that is indirectly
   referenced as a *global* through a function declared in the visible
   part of Q and applied in the ``initial_condition_aspect`` of Q must
   be initialized during the elaboration of Q.
#. A ``state_name`` cannot be referenced directly in an
   ``initial_condition_aspect`` of a package it can only be referenced
   indirectly via a function declared in the visible part of the
   package.
#. An ``initial_condition_aspect`` of a package Q shall not reference
   a *variable* or ``state_name`` of a package other than Q.

.. centered:: **Static Semantics**

#. The *boolean_*\ ``expression`` of an ``initial_condition_aspect``
   of a package is a predicate which defines the state of the package
   after its elaboration.

.. centered:: **Restrictions that may be Applied**
.. include:: restrictions-and-profiles.rst
   :start-after: 7.1.4 Initial Condition Aspect
   :end-before: END OF FILE 

.. centered:: **Dynamic Semantics**

There are no dynamic semantics associated with the
``initial_condition_aspect`` the rules are checked by static analysis.

.. centered:: **Verification Rules**

.. centered:: *Checked by Flow Analysis*

#. Each *variable* appearing in an ``initial_condition_aspect`` of a
   package Q which is declared in the visible part of Q must be
   initialized either at the point of declaration in Q or within the
   sequence of statements of the body of Q.
#. The state components represented by each ``state_name`` of a
   package Q which is indirectly referenced by a function appearing in
   the ``initial_condition_aspect`` Q must be initialized during the
   elaboration of Q.

.. todo:: I have not excluded the use of variables or functions of
   other packages in initial_conditions.  This may well give us
   elaboration order dependencies.  We need to think about this.  In
   the meantime I have a restriction to prohibit their use.

.. centered:: *Checked by Proof*

#. Verification conditions are generated for the declarations of a
   package and the sequence of statements of its body.  The
   verification conditions must be proven to show that the
   declarations and statement satisfy the predicate given in the
   ``initial_condition_aspect`` of the package.

.. todo:: Aspects for RavenSpark, e.g., Task_Object and Protected_Object



Package Bodies
--------------

State Refinement
^^^^^^^^^^^^^^^^

A package Q with an ``abstract_state_aspect`` must have a
``refined_state_aspect`` appearing in the ``aspect_specification`` of
the body of Q.  The ``refined_state_aspect`` lists for each
``state_name``, its *constituents*.  A constituent is either a
*variable* or another ``state_name``.

If a constituent is a *variable* it must be visible at
the place it is used and declared:

 * immediately within the ``private_part`` or body of Q,
 * in the ``visible_part`` of package embedded in Q, or,
 * in the ``visible_part`` of a private child of Q.

if the constituent is a ``state_name`` it must be visible and be
declared in a ``abstract_state_aspect`` of:

 * a package embedded within Q, or,
 * a private child of Q.

In the body of package Q the body of subprogram P must refine its
``global_aspect`` and ``dependency_aspect`` in terms of each
``constituent`` of each ``state_name`` mentioned in its declaration.
Expression functions are excluded from this rule because the
refinement may be deduced from the defining expression.

Global and dependency refinement are defined using a
``refined_global_aspect`` and a ``refined_depends_aspect``
respectively.

If a subprogram P declared in the visible part of package Q has a
``state_name`` of Q mentioned in its ``global_aspect`` then a refined
pre and post condition may be given on the body of P in terms of the
constituents of the ``state_name`` using a
``refined_precondition_aspect`` and a
``refined_postcondition_aspect``.


Refined State Aspect
^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

  refined_state_aspect   ::= Refined_State => refined_state_list
  refined_state_list     ::= (state_and_constituents {, state_and_constituents})
  state_and_constituents ::= state_name => constituent_list
  constituent_list       ::= constituent
                           | (constituent_definition {, constituent_definition)
  constituent_definition ::= constituent [=> (Volatile => mode_selector)]

where

  ``constituent ::=`` *variable_*\ ``name | state_name``

.. centered:: **Legality Rules**

#. If a package specification has an ``abstract_state_aspect`` then
   its body must have a ``refined_state_aspect``.
#. A package body cannot have a ``refined_state_aspect`` if its
   specification does not have an ``abstract_state_aspect``.
#. For each ``state_name`` appearing in an ``abstract_state_aspect``
   in the specification of a package Q, there must be a
   ``state_and_constituents`` naming the ``state_name`` in the
   ``refined_state_aspect`` in the body of Q.
#. Each ``state_name`` appearing in the ``abstract_state_aspect`` of a
   package Q must appear exactly once as the ``state_name`` of a
   ``state_and_constituents`` in the ``refined_state_list`` of the the
   ``refined_state_aspect``.
#. A ``state_name`` declared in the ``abstract_state_aspect`` of a
   package cannot appear as a ``constituent`` in the
   ``refined_state_aspect`` in the body of the package.
#. A *variable* declared in the visible part of a package Q is not a
   ``constituent`` of Q and cannot appear in the
   ``refined_state_aspect`` in the body of Q.
#. Each ``constituent`` of the hidden state of must appear exactly
   once in a ``constituent_list`` of exactly one
   ``state_and_constituents``.  A constituent of a package Q is:

   * A *variable* declared in the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a package
     declared immediately within the ``private_part`` or body of Q;
   * A *variable* declared in the ``visible_part`` of a private child
     package of Q;
   * A ``state_name`` declared in the ``abstract_state_aspect`` of a
     package declared immediately within the body of a package Q; and
   * A ``state_name`` declared in the ``abstract_state_aspect`` of a
     private child package of Q,

#. A *variable* which is a ``constituent`` is an *entire variable*; it
   is not a component of a containing object.

.. centered:: **Static Semantics**

#. If a package Q does not have an explicit ``abstract_state_aspect``
   given but it has state ``constituents`` then an implicit
   ``abstract_state_aspect`` containing just a single ``state_name`` S
   will be assumed in which all the constituents of Q are constituents
   of S.  S is an assumed ``state_name`` and cannot be explicitly be
   referenced.  This will restrict the extent of the static analyses
   and proof possible.

.. todo:: Refinment rules for external variables, rules for refinement
   using nested and private packages



Refined Global Aspect
^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

  refined_global_aspect ::= Refined_Global => mode_refinement

.. centered:: **Static Semantics**

#. A ``refined_global_aspect`` may only appear on the body of a
   subprogram P in a package whose ``visible_part`` contains the
   declaration of P which has a ``global_aspect``.
#. A ``refined_global_aspect`` on the body of a subprogram P may only
   mention ``constituents`` of a ``state_name`` mentioned in the
   ``global_aspect`` in the declaration of P or a *global variable*
   named in the the ``global_aspect`` of P.
#. The modes of the constituents of a ``state_name`` S in a
   ``refined_global_aspect`` of body of a subprogram must be
   compatible with the mode given to S in the ``global_aspect`` of the
   subprogram declaration.  If the mode of S is **in** then all of the
   ``constituents`` of S must be mode **in**.  If S is mode **out**
   then all the ``constituents`` of S must be mode **out**.  If S is
   mode **in out** then at least one of the ``constituents`` must be
   mode **in** or **in out** and at least one of the ``constituents``
   must be mode **out** or **in out**.
#. The mode of a *global variable* G in a ``refined_global_aspect`` of
   a body of a subprogram must be identical to the mode of G in the
   ``global_aspect`` of the subprogram declaration.

.. centered:: **Restrictions that may be Applied**

#. The restriction ``Moded_Variables_Are_Entire`` asserts that a
   ``Moded_item`` cannot be a subcomponent name.
#. The restriction ``No_Conditional_Modes`` prohibits the use of a
   ``conditional_mode`` in a ``mode_specification``.

Refined Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

::

  refined_depends_aspect ::= Refined_Depends => dependency_relation

.. centered:: **Static Semantics**

#. A ``refined_dependency_aspect`` may only appear on the body of a
   subprogram P in a package whose ``visible_part`` contains the
   declaration of P which has a ``global_aspect``.
#. A ``refined_dependency_aspect`` on the body of a subprogram P may
   only mention ``constituents`` of a ``state_name`` mentioned in the
   ``global_aspect`` in the declaration of P, a *global variable*
   named in the the ``global_aspect`` of P or a *formal parameter* of
   P.
#. A constituent of a ``state_name`` or a *global variable* appearing
   in a ``refined_global_aspect`` of a subprogram body may be an
   ``import`` or an ``export`` dependent on its mode.  Similarly a
   *formal_parameter* of the subprogram may be an ``import`` or an
   ``export`` depending on its mode.
#. The rules for what may be an ``import`` and what may be an
   ``export`` are the same as for a ``dependency_aspect`` accept that
   the ``refined_global_aspect`` of the subprogram is considered
   rather than the ``global_aspect``.

.. centered:: **Dynamic Semantics**

Abstractions do not have dynamic semantics.

Refined Precondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

``refined_precondition_aspect ::= Refined_Pre =>`` *Boolean_*\ ``expression``

.. centered:: **Static Semantics**

#. A ``refined_precondition`` may only appear on the body of a
   subprogram.
#. The *boolean_*\ ``expression`` of a ``refined_precondition`` of a
   subprogram body may only reference a *variable* if it is a *formal
   parameter* of the subprogram and if the subprogram has:

  #.  a ``refined_global_aspect``, then the *variable* must be a
      *global variable* including a ``constituent`` which is a
      *variable* of the ``refined_global_aspect``;
  #. a ``global_aspect`` but no ``refined_global_aspect``, then the
     *variable* must be a *global variable* of the ``global_aspect``;
     or
  #. no ``global_aspect``, then no *global variables* may be
     referenced in a ``refined-precondition``.

.. centered:: **Proof Semantics**

#. The precondition of a subprogram declaration shall imply the the
   ``refined_precondition``

.. centered:: **Dynamic Semantics**

#. The call of a subprogram with a ``refined_precondition`` needs to
   satisfy the expression (**if** precondition **then**
   ``refined_precondition`` **else** ``false``) otherwise the
   constraint error Assertions.Assertion_Error is raised.  The
   precondition is evaluated in the context of the calling environment
   whereas the ``refined_precondition`` is evaluated in the context of
   the body of the subprogram.

Refined Postcondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. centered:: **Syntax**

``refined_postcondition_aspect ::= Refined_Post =>`` *Boolean_*\
``expression``

.. centered:: **Static Semantics**

#. A ``refined_precondition`` may only appear on the body of a
   subprogram.
#. The *boolean_*\ ``expression`` of a ``refined_precondition`` of a
   subprogram body may only reference a *variable* if it is a *formal
   parameter* of the subprogram and if the subprogram has:

  #.  a ``refined_global_aspect``, then the *variable* must be a
      *global variable* including a ``constituent`` which is a
      *variable* of the ``refined_global_aspect``;
  #. a ``global_aspect`` but no ``refined_global_aspect``, then the
     *variable* must be a *global variable* of the ``global_aspect``;
     or
  #. no ``global_aspect``, then no *global variables* may be
     referenced in a ``refined-precondition``.

.. centered:: **Proof Semantics**

#. The precondition and the ``refined_precondition`` and the
   ``refined_postcondition`` of a subprogram declaration shall imply
   the postcondition.

.. centered:: **Dynamic Semantics**

#. The call of a subprogram with a ``refined_postcondition`` needs to
   satisfy the expression (**if** ``refined_postcondition`` **then**
   postcondition **else** ``false``) otherwise the constraint error
   Assertions.Assertion_Error is raised.  The
   ``refined_postcondition`` is evaluated in the context of the body
   of the subprogram whereas the postcondition is evaluated in the
   context of the calling environment.

.. todo:: Class wide pre and post conditions.

.. todo:: package dependencies: circularities, private/public child
     packages and their relationship with their parent especially in
     regard to data abstraction.

Private Types and Private Extensions
------------------------------------

.. centered:: **Extended Static Semantics**

#. The partial view of a private type or private extension may be in
   |SPARK| even if its full view is not in |SPARK|. The usual rule
   applies here, so a private type without discriminants is in
   |SPARK|, while a private type with discriminants is in |SPARK| only
   if its discriminants are in |SPARK|.

Private Operations
^^^^^^^^^^^^^^^^^^


Type Invariants
^^^^^^^^^^^^^^^

.. centered:: **Extended Dynamic Semantics**

#. The Ada 2012 RM lists places at which an invariant check is performed. In
   |SPARK|, we add the following places:

   * Before a call on any subprogram or entry that:

     * is explicitly declared within the immediate scope of type T (or
       by an instance of a generic unit, and the generic is declared
       within the immediate scope of type T), and

     * is visible outside the immediate scope of type T or overrides
       an operation that is visible outside the immediate scope of T,
       and

     * has one or more in out or in parameters with a part of type T.

     the check is performed on each such part of type T.
