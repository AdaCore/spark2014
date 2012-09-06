.. _abstraction of global state:

Abstraction of State
====================

The *variables* declared in a package Q, embedded packages declared within Q, and the private children of Q constitute the state of a package.  The *variable* declarations are only visible to users of Q if they are declared in the ``visible_part`` of Q which is not good practice.  The declarations of all other variables are hidden from the user of Q.  Though the variables are hiddedn they still form part (or all) of the state of Q and this state cannot be ignored for static analyses and proof.

Abstract State
--------------

An abstract state is a name representing the state embodied by the hidden *variables* of a package. The overall state of a package may be represented by one or more visible *variables* and abstract states.  An abstract state of a package has no type and may only be used within a ``global_aspect`` or a ``dependency_aspect``.  

If a subprogram P with a ``global_aspect`` is declared in the ``visible_part`` of a package and P reads or updates any of the hidden *variables* of the package then P must include in its ``global_aspect`` the abstract states with the correct mode that represent the hidden *variables* referenced by P.  If P has a ``dependency_apsect`` then the abstract states must appear as imports and exports, as appropriate, in the ``dependency_relation`` of the aspect.

An abstract state name is declared using a ``abstract_state_aspect``. 

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
#. A package shall only have an ``abstract_state_aspect`` if it has *variables* declared in its ``private_part``, immediately within its body, 

  name_state_property_list ::= defining_identifier [=> property]
  property_list            ::= property
                             | (property {, property})
  property               ::= Volatile => mode_selector
                           | A_Task
                           | Is_Protected => protected_feature_list
  protected_feature_list ::= (protected_feature {, protected_feature})
  protected_feature      ::= Priority => expression
                           | Suspendable
                           | Interrupt [=> name_pair_list]
                           | Protects => identifier_list
  name_pair
                            

If a subprogram delared in the ``visible_p 
A type that represents global state of, e.g., a package, can be defined as
follows::

   type T is new SPARK.Abstract_Type;

Variables representing such a state can then be defined at package level::

   V : T;

Such variables are only accessible in aspects such as ``Global_(In/Out)`` and
``Derives``, but not in programs nor in contracts.

Each such abstract variable is associated to a set of (private or public)
global variables. This association is established at the point of declaration
of each non-abstract global variable::

   X : Integer
      with Refines => V;
   Z : Boolean
      with Refines => V;

As the aspect name indicates, we also say that ``V`` is *refined* to contain
``X`` and ``Z``.

Proof semantics
---------------

Abstract variables stand for the set of associated concrete variables. When a
subprogram has ``Global`` or ``Derives`` aspects on its specification *and*
its body, it is checked that the aspects on the body refine the aspects on the
specification. This means that once the abstract variables are replaced by
the concrete variables, the former contains the latter.

Dynamic Semantics
-----------------

Abstractions do not have dynamic semantics.

Discussion
----------

It has been argued that with this proposition, it is hard to see the set of
variables that an abstract variable refines to. From this point of view,
declaring the refinement at the abstract variable is preferable, e.g.::

   V : T
      with Refinement => (X, Y, Z);

But this has a number of problems, the most difficult one being that the
concrete variables may be defined in the body only, which would make it
necessary to parse the body to understand the refinement aspect.

How can one declare that an abstract state refines to the abstract state of
another package?
