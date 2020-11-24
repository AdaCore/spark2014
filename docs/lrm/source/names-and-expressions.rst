Names and Expressions
=====================

.. index:: assertion expression

The term *assertion expression* denotes an expression that appears inside an
assertion, which can be a pragma Assert, a precondition or postcondition, a
type invariant or (subtype) predicate, or other assertions introduced in |SPARK|.

Names
-----

No extensions or restrictions.

Indexed Components
~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Slices
~~~~~~

No extensions or restrictions.

Selected Components
~~~~~~~~~~~~~~~~~~~

Some constructs which would unconditionally raise an exception at
run time in Ada are rejected as illegal in |SPARK| if this property
can be determined prior to formal program verification.

.. centered:: **Legality Rules**


1. If the prefix of a record component selection is known statically
   to be constrained so that the selected component is not present,
   then the component selection (which, in Ada, would raise
   Constraint_Error if it were to be evaluated) is illegal.


Attributes
~~~~~~~~~~

Many of the Ada language defined attributes are in |SPARK| but there
are exclusions.  For a full list of attributes supported by |SPARK| see
:ref:`language_defined_attributes`.

A |SPARK| implementation is permitted to support other attributes
which are not Ada or |SPARK| language defined attributes and these
should be documented in the User Guide for the tool.

.. centered:: **Legality Rules**

.. index:: Access

1. The prefix of the attribute Access shall be the name of a subprogram.

2. A subprogram used as the prefix of a reference to the attribute Access:

   - shall not be declared within a protected type or object;

   - shall not be a dispatching operation of a tagged type; and

   - shall not be a declared in the scope of a type with an invariant
     if this type is mentioned in the subprogram's profile unless it is
     a boundary subprogram (see section 7.3.2 for the definition of a
     boundary subprogram).

3. The Volatile_Function aspect of a subprogram used as the prefix of a
   reference to the attribute Access, if specified, shall not be True
   (see section 7.1.2 for the definition of Volatile_Function).

.. centered:: **Verification Rules**

4. The prefix of the Access attribute shall have no global inputs and outputs
   (see section 6.1 for inputs and outputs of subprograms).

.. index:: verification condition; for Access on subprogram

5. On a reference to the Access attribute, a verification condition is
   introduced to ensure that the precondition of the prefix of the attribute
   is implied by the precondition of its expected type. Similarly,
   a verification condition is introduced to ensure that the postcondition of
   the expected type is implied by the postcondition of the prefix of the
   attribute.


User-Defined References
~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**


1. User-defined references are not allowed.


2. The aspect Implicit_Dereference is not permitted.


User-Defined Indexing
~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**


1. User-defined indexing is not allowed.


2. The aspects Constant_Indexing and Variable_Indexing are not
   permitted.


Literals
--------

No extensions or restrictions.


Aggregates
----------

.. centered:: **Legality Rules**


1. The box symbol, <>, shall not be used in an aggregate unless the type(s)
   of the corresponding component(s) define full default initialization.


2. If the ``ancestor_part`` of an ``extension_aggregate``
   is a ``subtype_mark``, then the type of the denoted subtype
   shall define full default initialization.


[The box symbol cannot be used in an aggregate to produce an uninitialized
scalar value or a composite value having an uninitialized scalar value as a
subcomponent. Similarly for an ancestor subtype in an extension aggregate.]

.. _expressions:

Expressions
-----------

.. index:: side-effects

An expression is said to be *side-effect free* if the evaluation of the
expression does not update any object.  The evaluation of an expression
free from side-effects only retrieves or computes a value.

.. centered:: **Legality Rules**


1. An expression shall be side-effect free.
   [Strictly speaking, this "rule" is a consequence of other rules,
   most notably the rule that a function cannot have outputs other
   than its result.]

.. index:: expression with a variable input; disallowed contexts

2. An expression (or range) in |SPARK| occurring in certain contexts
   (listed below) shall not have a variable input. This means that
   such an expression shall not read a variable, nor shall it call a
   function which (directly or indirectly) reads a variable. These
   contexts include:

    * a constraint other than the range of a loop parameter
      specification (see :ref:`subtype_declarations`);

    * the default_expression of a component declaration (see
      :ref:`record_types`);

    * the default_expression of a discriminant_specification
      (see :ref:`discriminants`);

    * a Dynamic_Predicate aspect specification
      (see :ref:`subtype_predicates`);

    * a Type_Invariant aspect specification
      (see :ref:`type_invariants`);

    * an indexing expression of an indexed_component or the discrete_range of a
      slice in an object renaming declaration which renames part of that
      indexed_component or slice (see :ref:`object_renaming_declarations`);

    * a generic actual parameter corresponding to a generic formal object
      having mode **in** (see :ref:`generic_instantiation`);

    * the borrowed name of the expression of an object declaration defining a
      borrowing operation, except for a single occurrence of the root object
      of the expression (see :ref:`access-types`).

except when the context itself occurs within a declare expression.

[An expression in one of these contexts may read a constant
which is initialized with the value of a variable.]

[These rules simplify analysis by eliminating the need to deal with
implicitly created anonymous constants. An expression which does not
have a variable input will always yield the same result if it is
(conceptually, for purposes of static analysis) reevaluated later.
This is not true of an expression that has a variable input because the
value of the variable might have changed.]

[For purposes of these rules, the current instance of a type or subtype is
not considered to be a variable input in the case of a Dynamic_Predicate
or Type_Invariant condition, but is considered to be a variable
input in the case of the default_expression of a component declaration.]

.. index:: portability; order of evaluation and overflows

Operators and Expression Evaluation
-----------------------------------

Ada grants implementations the freedom to reassociate a sequence
of predefined operators of the same precedence level even if this
changes the behavior of the program with respect to intermediate
overflow (see Ada RM 4.5). |SPARK| assumes that an implementation
does not take advantage of this permission; in particular,
a proof of the absence of intermediate overflow in this situation
may depend on this assumption.

A |SPARK| tool is permitted to provide a warning where operators may
be re-associated by a compiler.

[The GNAT Ada compiler does not take advantage of this permission.
The GNAT compiler also provides an option for rejecting constructs to
which this permission would apply. Explicit parenthesization can
always be used to force a particular association in this situation.]

Type Conversions
----------------

No extensions or restrictions.


Qualified Expressions
---------------------

No extensions or restrictions.


Allocators
----------

.. centered:: **Legality Rules**

.. index:: full default initialization; in allocators

1. The designated type of the type of an uninitialized allocator
   shall define full default initialization.

.. index:: non-interfering context; for allocators

2. Evaluation of an allocator is subject to the same restrictions as calling a
   volatile function (e.g., an allocator is not allowed within a non-volatile
   function). [If it seems helpful, an allocator may be thought of as being
   like a call to a volatile function which returns the access value
   designating the allocated object.]


3. The type of an allocator shall not be anonymous.


Static Expressions and Static Subtypes
--------------------------------------

No extensions or restrictions.
