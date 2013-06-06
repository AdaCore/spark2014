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

Use Clauses
-----------

Use clauses are always in |SPARK|, even if the unit mentioned is not completely
in |SPARK|.

Renaming Declarations
---------------------


Object Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An ``object_renaming_declaration`` for an entire object or a component of a
record introduces a static alias of the renamed object. As the
alias is static, in |SPARK| analysis it is replaced by the renamed object.
This scheme works over multiple levels of renaming.

In an ``object_renaming_declaration`` which renames the result of a function
the name of the declaration denotes a read only variable which is assigned the
value of the function result from the elaboration of the
``object_renaming_declaration``. This read only variable is used in |SPARK|
analysis.


Exception Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Package Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Subprogram Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


.. centered:: **Syntax**

There is no additional syntax associated with subprogram renaming declarations in |SPARK|.

.. centered:: **Legality Rules**

#. The ``aspect_specification`` on a ``subprogram_renaming_declaration`` shall not
   include any of the |SPARK|-defined aspects introduced in this document. [This restriction
   may be relaxed in the future.]

.. centered:: **Static Semantics**

There are no additional static semantics associated with subprogram renaming declarations in |SPARK|.

.. centered:: **Dynamic Semantics**

There are no additional dynamic semantics associated with subprogram renaming declarations in |SPARK|.

.. centered:: **Verification Rules**

There are no additional verification rules associated with subprogram renaming declarations in |SPARK|.

[Note that, from the point of view of both static and dynamic verification,
a *renaming-as-body* is treated as a one-line subprogram that "calls through" to the renamed unit.]


Generic Renaming Declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


The Context of Overload Resolution
----------------------------------

No extensions or restrictions.
