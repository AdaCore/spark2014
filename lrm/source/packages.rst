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
represent the hidden *variables* referenced by P.  If P has a
``dependency_aspect`` then the abstract states must appear as imports
and exports, as appropriate, in the ``dependency_relation`` of the
aspect.

An abstract ``state_name`` is declared using a
``abstract_state_aspect`` appearing in an ``aspect_specification`` of
a ``package_specification``.

.. centered:: **Syntax**

::

  abstract_state_aspect ::= Abstract_State => abstract_state_list
  abstract_state_list   ::= state_name
                          | (state_name {, state_name})
  state_name            ::= defining_identifier [=> (Volatile => mode_selector)]

.. centered:: **Static Semantics**

#. An ``abstract_state_aspect`` may only be placed in a
   ``aspect_specification`` of a ``package_specification``.
#. At most one ``abstract_state_aspect`` may appear in a single
   ``aspect_specification``.
#. The ``defining_identifier`` of a ``state_name`` must not be the
   same as a directly visible name or a name declared immediately
   within the package containing the ``abstract_state_aspect``.
#. The ``defining_identifier`` of a ``state_name`` shall not be
   repeated within the ``abstract_state_list``.
#. A package shall only have an ``abstract_state_aspect`` if it has
   *variables* declared in its ``private_part``, immediately within
   its body, or within embedded packages or private child packages.
#. A ``state_name`` has the same scope and visibility as a declaration
   in the ``visible part`` of the package to which the
   ``abstract_state_aspect`` is applied.
#. A ``state_name`` can only appear in a ``global_aspect`` or a
   ``dependency_aspect``, their refinded counterparts, or their
   equivalent pragmas.

.. centered:: **Restrictions that may be Applied**

#. ``Abstract_State_Names_required`` enforces the restriction that a
   package which has hidden state must have an
   ``abstract_state_aspect``.
#. ``No In_Out Volatile Variables`` enforces the restriction that a
   ``mode_selector`` of In_Out may not appear in an
   ``abstract_state_aspect`` or a ``refined_state_aspect``.


.. todo:: Initializes, Initial_Condition aspects.

.. todo::  Aspects for RavenSpark, e.g., Task_Object and Protected_Object

.. todo:: External variables.



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

.. centered:: **Static Semantics**

#. If a package specification has an ``abstract_state_aspect`` then
   its body must have a ``refined_state_aspect``.
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
#. A *variable* declared in the ``private_part`` or body of a package
   is a ``constituent`` of the package.
#. A *variable* declared in the ``visible_part`` of a package declared
   immediately within the ``private_part`` or body of a package Q is a
   ``constituent`` of Q.
#. A *variable* declared in the ``visible_part`` of a private child
   package of a package Q is a ``constituent`` of Q.
#. A *variable* which is a ``constituent`` is an *entire variable*; it
   is not a component of a containing object.
#. A ``state_name`` declared in the ``abstract_state_aspect`` of a
   package declared immediately within the ``private_part`` or body of
   a package Q is a ``constituent`` of Q.
#. A ``state_name`` declared in the ``abstract_state_aspect`` of a
   private child package of a package Q is a ``constituent`` of Q.
#. Each ``constituent`` of a package Q is a constituent of a single
   ``state_name`` declared in the ``aspect_state_aspect`` of Q.
#. For a package Q with an ``abstract_state_aspect``, all the
   *variables* and ``state_names`` which are ``constituents`` of Q
   must appear in exactly one ``constituent_list`` of the
   ``refined_state_aspect`` of Q.
#. If a package Q does not have an explicit ``abstract_state_aspect``
   given but it has state ``constituents`` then an implicit
   ``abstract_state_aspect`` containing just a single ``state_name`` S
   will be assumed in which all the constituents of Q are constituents
   of S.  S is an assumed ``state_name`` and cannot be explicitly be
   referenced.  This will restrict the extent of the static analyses
   available.
#. if the specification of a package Q does not have a
   ``abstract_state_aspect`` then the body of Q shall not have a
   ``state_refinement_aspect``.

.. centered:: **Restrictions that may be Applied**


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

