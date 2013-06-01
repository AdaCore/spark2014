Names and Expressions
=====================

We denote by *assertion expression* an expression that appears inside an
assertion, which can be a pragma Assert, a precondition or postcondition, a
type invariant or predicate, or a contract case.

Names
-----

A name that denotes an entity is in Alfa if and only if the entity is in
Alfa. Neither ``explicit_dereference`` nor ``implicit_dereference`` are in
Alfa.

Attribute ``Access`` is not in Alfa. As they are based on access discriminants,
user-defined references and user-defined indexing are not in Alfa.

Literals
--------

The literal **null** is not in Alfa.

Aggregates
----------

Outside of assertion expressions, an aggregate is in Alfa only if its type is
in Alfa and it is pure. Inside assertion expressions, aggregates in Alfa must
additionally be fully defined. An aggregate which leaves subcomponents
uninitialized is not in Alfa if it appears inside an assertion expression.

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
