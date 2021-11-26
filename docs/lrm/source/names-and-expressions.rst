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

.. container:: heading

   Legality Rules


1. If the prefix of a record component selection is known statically
   to be constrained so that the selected component is not present,
   then the component selection (which, in Ada, would raise
   Constraint_Error if it were to be evaluated) is illegal.


Attributes
~~~~~~~~~~

Many of the Ada language defined attributes are in |SPARK| but there
are exclusions.  For a full list of attributes supported by |SPARK| see
:ref:`Language-Defined Attributes`.

A |SPARK| implementation is permitted to support other attributes
which are not Ada or |SPARK| language defined attributes and these
should be documented in the User Guide for the tool.

.. container:: heading

   Legality Rules

.. index:: Access

1. The prefix of an Access attribute reference shall be the name of a subprogram
   or a name denoting an object whose root object is either a standalone object
   or a subprogram parameter (see section 3.10 for the definition of a
   the root object of a name denoting an object).

2. A subprogram used as the prefix of an Access attribute reference:

   - shall not be declared within a protected type or object;

   - shall not be a dispatching operation of a tagged type; and

   - shall not be a declared in the scope of a type with an invariant
     if this type is mentioned in the subprogram's profile unless it is
     a boundary subprogram (see section 7.3.2 for the definition of a
     boundary subprogram).

3. The Volatile_Function aspect of a subprogram used as the prefix of an
   Access attribute reference, if specified, shall not be True
   (see section 7.1.2 for the definition of Volatile_Function).

4. A reference to the Access attribute whose type is an anonymous
   access-to-object type or a named access-to-variable type shall occur
   directly inside a stand-alone object declaration, an assignment, or a
   return statement.

5. The prefix of an Access attribute reference whose type is a named
   access-to-constant type shall either be a name denoting a part of a
   stand-alone constant whose type is neither a named access-to-variable type
   nor an anonymous access-to-object type, or shall
   include a dereference whose prefix has a named access-to-constant type.

.. container:: heading

   Verification Rules

6. A subprogram used as the prefix of an Access attribute reference shall have
   no global inputs and outputs (see section 6.1 for inputs and outputs of
   subprograms).

.. index:: verification condition; for Access on subprogram

7. On an Access attribute reference whose prefix is the name of a subprogram, a
   verification condition is introduced to ensure that the precondition of the
   prefix of the attribute reference is implied by the precondition of
   its expected type. Similarly, a verification condition is introduced to
   ensure that the postcondition of the expected type is implied by the
   postcondition of the prefix of the attribute reference.


User-Defined References
~~~~~~~~~~~~~~~~~~~~~~~

.. container:: heading

   Legality Rules


1. User-defined references are not allowed.


2. The aspect Implicit_Dereference is not permitted.


User-Defined Indexing
~~~~~~~~~~~~~~~~~~~~~

.. container:: heading

   Legality Rules


1. User-defined indexing is not allowed.


2. The aspects Constant_Indexing and Variable_Indexing are not
   permitted.


Literals
--------

No extensions or restrictions.


Aggregates
----------

.. container:: heading

   Legality Rules


1. The box symbol, <>, shall not be used in an aggregate unless the type(s)
   of the corresponding component(s) define full default initialization.


2. If the ``ancestor_part`` of an ``extension_aggregate``
   is a ``subtype_mark``, then the type of the denoted subtype
   shall define full default initialization.


[The box symbol cannot be used in an aggregate to produce an uninitialized
scalar value or a composite value having an uninitialized scalar value as a
subcomponent. Similarly for an ancestor subtype in an extension aggregate.]

Expressions
-----------

.. index:: side-effects

An expression is said to be *side-effect free* if the evaluation of the
expression does not update any object.  The evaluation of an expression
free from side-effects only retrieves or computes a value.

.. container:: heading

   Legality Rules


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
      specification (see :ref:`Subtype Declarations`);

    * the default_expression of a component declaration (see
      :ref:`Record Types`);

    * the default_expression of a discriminant_specification
      (see :ref:`Discriminants`);

    * a Dynamic_Predicate aspect specification
      (see :ref:`Subtype Predicates`);

    * a Type_Invariant aspect specification
      (see :ref:`Type Invariants`);

    * an indexing expression of an indexed_component or the discrete_range of a
      slice in an object renaming declaration which renames part of that
      indexed_component or slice, or a prefix of a dereference (either
      implicit or explicit) in an object renaming declaration which renames
      part of the designated object (see :ref:`Object Renaming Declarations`);

    * a generic actual parameter corresponding to a generic formal object
      having mode **in** (see :ref:`Generic Instantiation`);

    * the borrowed name of the expression of an object declaration defining a
      borrowing operation, except for a single occurrence of the root object
      of the expression (see :ref:`Access Types`).

except when the context itself occurs within a declare expression. For purposes
of the above rule, a generic actual parameter corresponding to a generic formal
object of mode **in out** is considered to be an object renaming declaration
which renames the named object.

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

.. index:: allocating function

A function is said to be an *allocating function* if the result type of the
function is a named access-to-variable type or a composite owning type (see
section :ref:`Access Types`). [Redundant: The only functions with a result of
an owning type in SPARK are allocating functions and borrowing traversal
functions defined in section :ref:`Access Types`; a function cannot be both an
allocating function and a traversal function.]

.. container:: heading

   Legality Rules

.. index:: full default initialization; in allocators

1. The designated type of the type of an uninitialized allocator
   shall define full default initialization.

.. index:: allocating context
           memory leak; for expressions

2. An allocator or a call to an allocating function shall only occur in an
   *allocating context*. An expression occurs in an allocating context if
   it is:

   * the [right-hand side] expression of an assignment statement; or

   * the initialization expression of an object declaration
     which does not occur inside a declare expression; or

   * the return expression of a ``simple_return_statement``; or

   * the expression of the ``extended_return_object_declaration``
     of an ``extended_return_statement``; or

   * the expression of a type conversion, a qualified expression or a
     parenthesized expression occurring in an allocating context; or

   * the expression corresponding to a component value in an aggregate
     occurring in an allocating context; or

   * the expression of an initialized allocator; or

   * inside an assertion.

   [This restriction is meant to prevent storage leaks, together with the rules
   on owning access objects, see section :ref:`Access Types`. Note that
   allocators or calls to allocating functions inside assertions are allowed,
   but should be reported by the analysis tool as leading to a memory leak. In
   practice, such memory leaks cannot happen if the corresponding assertions
   are not enabled in the final executable.]

3. The type of an allocator shall not be anonymous.


Static Expressions and Static Subtypes
--------------------------------------

No extensions or restrictions.
