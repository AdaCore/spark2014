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


1. Use clauses are always in |SPARK|, even if the unit mentioned is
   not completely in |SPARK|.


Renaming Declarations
---------------------


Object Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**


1. [An expression or range occurring as part of an
   ``object_renaming_declaration`` shall not have a variable input;
   similarly, the access-valued prefix of a dereference occurring
   as part of an object_renaming declaration shall not have a
   variable input. See :ref:`Expressions` for the statement of this rule.]
   [The first part of this rule can apply to an index of an
   indexed_component and the range of a slice.]


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


1. The ``aspect_specification`` on a ``subprogram_renaming_declaration`` shall not
   include any of the |SPARK|-defined aspects introduced in this document.

.. todo:: Consider relaxing this restriction.


Generic Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


The Context of Overload Resolution
----------------------------------

No extensions or restrictions.
