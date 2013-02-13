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

No extensions or restrictions.

An ``object_renaming_declaration`` for an entire object or a component of a
record introduces a static alias of the renamed object. As the
alias is static, in |SPARK| analysis it is replaced by the renamed object. 
This scheme works over multiple levels of renaming.

In an ``object_renaming_declaration`` which renames the result of a function 
the name of the declaration denotes a read only variable which is assigned the 
value of the function result from the elaboration of the 
``object_renaming_declaration``. This read only variable is used in |SPARK| 
analysis.

.. todo:: Describe model of renaming for array indexing and slices.
          To be completed in the Milestone 3 version of this document.


Note that, from the point of view of both static and dynamic verification,
a *renaming-as-body* is treated as
a one-line subprogram that "calls through" to the renamed unit. 

The Context of Overload Resolution
----------------------------------

No extensions or restrictions.
