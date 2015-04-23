Visibility Rules
================

Declarative Region
------------------

No extensions or restrictions.

Scope of Declarations
---------------------

No extensions or restrictions.

Visibility
----------

No extensions or restrictions.

Overriding Indicators
~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Use Clauses
-----------

.. centered:: **Legality Rules**

.. _tu-use_clauses-01:

1. Use clauses are always in |SPARK|, even if the unit mentioned is
   not completely in |SPARK|.

.. _etu-use_clauses:

Renaming Declarations
---------------------


Object Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Static Semantics**

.. _tu-object_renaming_declarations-01:

1. An expression or range occurring as part of an
   ``object_renaming_declaration`` shall not have a variable input.
   [This rule can apply to an index of an indexed_component and the range
   of a slice.] [This rule avoids the possible dependence of a subprogram
   on an unnamed constant that cannot be mentioned in dependency contracts,
   and it ensures that the renamed object can be mentally replaced for the
   renaming variable in code reviews.]

.. _etu-object_renaming_declarations:

Exception Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Package Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Subprogram Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

From the point of view of both static and dynamic verification, a
*renaming-as-body* is treated as a one-line subprogram that "calls
through" to the renamed unit.

.. centered:: **Legality Rules**

.. _tu-subprogram_renaming_declarations-01:

1. The ``aspect_specification`` on a ``subprogram_renaming_declaration`` shall not
   include any of the |SPARK|-defined aspects introduced in this document.

.. todo:: Consider relaxing this restriction.

.. _etu-subprogram_renaming_declarations:

Generic Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


The Context of Overload Resolution
----------------------------------

No extensions or restrictions.
