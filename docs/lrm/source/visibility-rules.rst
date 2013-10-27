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

.. centered:: **Legality Rules**

.. _tu-overriding_indicators-01:

1. Tagged types are not couurently permitted in |SPARK| and therefore
   neither are overriding indicators permitted.

.. _etu-overriding_indicators-01:

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

1. An ``object_renaming_declaration`` for an entire object or a
   component of a record introduces a static alias of the renamed
   object. As the alias is static, in |SPARK| analysis it is replaced
   by the renamed object.  This scheme works over multiple levels of
   renaming.

.. _tu-object_renaming_declarations-02:

2. In an ``object_renaming_declaration`` which renames the result of a
   function the name of the declaration denotes a read only variable
   which is assigned the value of the function result from the
   elaboration of the ``object_renaming_declaration``. This read only
   variable is used in |SPARK| analysis.


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
