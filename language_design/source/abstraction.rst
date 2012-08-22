.. _abstraction of global state:

Abstraction of Global State
===========================

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
