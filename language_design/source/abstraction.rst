.. _abstraction of global state:

Abstraction of State
====================

The *variables* declared in a package Q, embedded packages declared within Q, and the private children of Q constitute the state of a package.  The *variable* declarations are only visible to users of Q if they are declared in the ``visible_part`` of Q which is not good practice.  The declarations of all other variables are hidden from the user of Q.  Though the variables are hiddedn they still form part (or all) of the state of Q and this state cannot be ignored for static analyses and proof.

Abstract State
--------------

An abstract state is a name representing the state embodied by the hidden *variables* of a package. The overall state of a package may be represented by one or more visible *variables* and abstract states.  An abstract state of a package has no type and may only be used within a ``global_aspect`` or a ``dependency_aspect``.  

If a subprogram P with a ``global_aspect`` is declared in the ``visible_part`` of a package and P reads or updates any of the hidden *variables* of the package then P must include in its ``global_aspect`` the abstract states with the correct mode that represent the hidden *variables* referenced by P.  If P has a ``dependency_apsect`` then the abstract states must appear as imports and exports, as appropriate, in the ``dependency_relation`` of the aspect.

An abstract ``state_name`` is declared using a ``abstract_state_aspect`` appearing in an ``aspect_specification`` of a ``package_specification``.

A package Q with an ``abstract_state_aspect`` must have a ``refined_state_aspect`` appearing in the ``aspect_specification`` of the body of Q.  The ``refinded_state_aspect`` lists for each ``state_name``, its *constituents*.  A constituent is either a *variable* or another ``state_name``.  

If a constituent is a *variable* it must be visible and declared:

 * immediately within the ``private_part`` or body of Q,
 * in the ``visible_part`` of package embedded in Q, or,
 * in the ``visible_part`` of a private child of Q.

if the constituent is a ``state_name`` it must be visible and be declared in a ``abstract_state_aspect`` of:

 * a package embedded within Q, or,
 * a private child of Q.

A ``state_name`` of a package Q may appear in a ``global_aspect`` and a ``dependency_aspect`` of a subprogram P declared in the visible part of Q.  A ``state_name`` may also appear in the ``global_aspect`` and ``dependency_aspect`` of a subprogram calling P form a user of Q.

In the body of package Q the body ofsubprogram P must refine its ``global_aspect`` and ``dependency_aspect`` in terms of each ``constituent`` of each ``state_name`` mentioned in its declaration.  Expression functions are excluded from this rule because the refinement may be deduced from the defining expression.

Global and dependency refinement are defined using a ``refined_global_aspect`` and a ``refined_depends_aspect`` respectively.

If a suprogram P declared in the visible part of package Q has a ``state_name`` of Q mentioned in its ``global_aspect`` then a refined pre and post condition may be given on the body of P in terms of the constituents of the ``state_name`` us in a ``refined_precondition_aspect`` and a ``refined_postcondition_aspect.
 

Syntax of Abstract State Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::
  
  abstract_state_aspect ::= Abstract_State => abstract_state_list
  abstract_state_list   ::= state_name
                          | (state_name {, state_name})
  state_name            ::= defining_identifier [=> (Volatile => mode_selector)]

Static Semantics 
^^^^^^^^^^^^^^^^

#. An ``abstract_state_aspect`` may only be placed in a ``aspect_specification`` of a ``package_specification``.
#. At most one ``abstract_state_aspect`` may appear in a single ``aspect_specification``.
#. The ``defining_identifier`` of a ``state_name`` must not be the same as a directly visible name or a name declared immediately within the package conatining the ``abstract_state_aspect``.
#. The ``defining_identifier`` of a ``state_name`` shall not be repeated within the ``abstract_state_list``.
#. A package shall only have an ``abstract_state_aspect`` if it has *variables* declared in its ``private_part``, immediately within its body, or within embedded packages or private child packages.
#. A ``state_name`` has the same scope and visibility as a declaration in the ``visible part`` of the package to which the ``abstract_state_aspect`` is applied.  
#. A ``state_name`` can only appear in a ``global_aspect`` or a ``dependency_aspect``, or their equivalent pragmas.

Restrictions that may be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. ``No In_Out Volatile Variables`` enforces the restriction that a ``mode_selector`` of In_Out may not appear in an ``abstract_state_aspect`` or a ``refined_state_aspect``.

.. todo::  Aspects for RavenSpark, e.g., Task_Object and Protected_Object
 

Syntax of Refined State Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::
  
  refined_state_aspect   ::= Refined_State => refined_state_list
  refined_state_list     ::= (state_and_constituents {, state_and_constituents})
  state_and_constituents ::= state_name => constituent_list
  constituent_list       ::= constituent
                           | (constituent_definition {, constituent_definition)
  constituent_definition ::= constituent [=> (Volatile => mode_selector)]

where 
  
  ``constituent ::=`` *variable_*\ ``name | state_name``                      


Static Semantics 
^^^^^^^^^^^^^^^^
#. If a package specification has an ``abstract_state_aspect`` then its body must have a ``refined_state_aspect``. 
#. For each ``state_name`` appearing in an ``abstract_state_aspect`` in the specification of a package Q, there must be a ``state_and_constituents`` naming the ``state_name`` in the ``refined_state_aspect`` in the body of Q.
#. Each ``state_name`` appearing in the ``abstract_state_aspect`` of a package Q must appear exactly once as the ``state_name`` of a ``state_and_constituents`` in the ``refined_state_list`` of the the ``refined_state_aspect``.
#. A ``state_name`` declared in the ``abstract_state_aspect`` of a package cannot appear as a ``constituent`` in the ``refined_state_aspect`` in the body of the package.
#. A *variable* declared in the visible part of a package Q is not a ``constituent`` of Q and cannot appear in the ``refined_state_aspect`` in the body of Q.     
#. A *variable* declared in the ``private_part`` or body of a package is a ``constituent`` of the package.
#. A *variable* declared in the ``visible_part`` of a package declared immediately within the ``private_part`` or body of a package Q is a ``constituent`` of Q.
#. A *variable* declared in the ``visible_part`` of a private child package of a package Q is a ``constituent`` of Q.
#. A ``state_name`` declared in the  ``abstract_state_aspect`` of a package declared immediately within the ``private_part`` or body of a package Q is a ``constituent`` of Q.
#. A ``state_name`` declared in the ``abstract_state_aspect`` of a private child package of a package Q is a ``constituent`` of Q.
#. Each ``constituent`` of a package Q is a constituent of a single ``state_name`` declared in the ``aspect_state_aspect`` of Q. 
#. For a package Q with an ``abstract_state_aspect``, all the *variables* and ``state_names`` which are ``constituents`` of Q must appear in exactly one ``constituent_list`` of the ``refined_state_aspect`` of Q.
#. If a package Q does not have an explicit ``abstract_state_aspect`` given but it has state ``constituents`` then an implicit ``abstract_state_aspect`` containing just a single ``state_name`` S will be assumed in which all the constituents of Q are constituents of S.  S is an assumed ``state_name`` and cannot be explicitly be referenced.  This will restrict the extent of the static analyses available.
#. if the specification of a package Q does not have a ``abstract_state_aspect`` then the body oq shall not have a ``state_refinement_aspect``.
  

Restrictions that may be Applied
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

#. ``Abstract_State_Names_required`` enforces the restriction that a package which has state ``constituents`` must have an ``abstract_state_aspect``.


Syntax of Refined Global Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  refined_global_aspect ::= Refined_Global => mode_refinement

Each ``moded_item`` of the ``mode_refinement`` must be a ``constituent``.

Syntax of Refined Dependency Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  refined_depends_aspect ::= Refined_Depends => dependency_relation

Each ``import`` and ``export`` of the ``dependency_relation`` must be a ``constituent``.

Dynamic Semantics
-----------------

Abstractions do not have dynamic semantics.

Syntax of Refined Precondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

``refined_precondition_aspect ::= Refined_Pre =>`` *Boolean_*\ ``expression``
  
Syntax of Refined Postcondition Aspect
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

``refined_postcondition_aspect ::= Refined_Post =>`` *Boolean_*\ ``expression``


