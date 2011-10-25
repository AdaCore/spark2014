Names and Expressions
=====================

Names
-----

A name that denotes an entity is in Alfa if and only if the entity is in
Alfa. Both ``explicit_dereference`` and ``implicit_dereference`` are not in
Alfa.

Attribute ``Access`` is not in Alfa. As they are based on access discriminants,
user-defined references and user-defined indexing are not in Alfa.

Literals
--------

The literal **null** is not in Alfa.

Aggregates
----------

An aggregate is in Alfa only if its type is in Alfa and it is pure.

Expressions
-----------

An expression is in Alfa only if its type is in Alfa and it is pure.

Operators and Expression Evaluation
-----------------------------------

In Alfa, there can be no sequence of operators of the same precedence level. 
Parentheses must be used to impose specific associations.

Type Conversions
----------------

No specific restrictions.

Qualified Expressions
---------------------

No specific restrictions.

Allocators
----------

Allocators are not in Alfa.

Static Expressions and Static Subtypes
--------------------------------------

No specific restrictions.
