Names and Expressions
=====================

The term *assertion expression* denotes an expression that appears inside an
assertion, which can be a pragma Assert, a precondition or postcondition, a
type invariant or (subtype) predicate, or other assertions introduced in |SPARK|.

Names
-----

.. centered:: **Legality Rules**

.. _tu-names-01:

1. Neither ``explicit_dereference`` nor ``implicit_dereference`` are
   in |SPARK|.

.. _etu-names:

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

.. _tu-selected_components-01:

1. If the prefix of a record component selection is known statically
   to be constrained so that the selected component is not present,
   then the component selection (which, in Ada, would raise
   Constraint_Error if it were to be evaluated) is illegal.

.. _etu-selected_components:

Attributes
~~~~~~~~~~

Many of the Ada language defined attributes are in |SPARK| but there
are exclusions.  For a full list of attributes supported by |SPARK| see
:ref:`language_defined_attributes`.

A |SPARK| implementation is permitted to support other attributes
which are not Ada or |SPARK| language defined attributes and these
should be documented in the User Guide for the tool.

.. centered:: **Legality Rules**

.. _tu-attributed-01:

1. The prefix of a '*Access* ``attribute_reference`` shall be a constant
   without variable input. [This ensures that information flows through such
   access values only depend on assignments to the access objects, not
   assignments to the accessed objects. See :ref:`object-declarations`.]

.. _etu-attributes:

User-Defined References
~~~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-user_defined_references-01:

1. User-defined references are not allowed.

.. _tu-user_defined_references-02:

2. The aspect Implicit_Dereference is not permitted.

.. _etu-user_defined_references:

User-Defined Indexing
~~~~~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-user_defined_indexing-01:

1. User-defined indexing is not allowed.

.. _tu-user_defined_indexing-02:

2. The aspects Constant_Indexing and Variable_Indexing are not
   permitted.

.. _etu-user_defined_indexing:

Literals
--------

No extensions or restrictions.


Aggregates
----------

.. centered:: **Legality Rules**

.. _tu-aggregates-01:

1. The box symbol, <>, shall not be used in an aggregate unless the type(s)
   of the corresponding component(s) define full default initialization.

.. _tu-aggregates-02:

2. If the ``ancestor_part`` of an ``extension_aggregate``
   is a ``subtype_mark``, then the type of the denoted subtype
   shall define full default initialization.

.. _etu-aggregates:

[The box symbol cannot be used in an aggregate to produce an uninitialized
scalar value or a composite value having an uninitialized scalar value as a
subcomponent. Similarly for an ancestor subtype in an extension aggregate.]

.. _expressions:

Expressions
-----------

An expression is said to be *side-effect free* if the evaluation of the
expression does not update any object.  The evaluation of an expression
free from side-effects only retrieves or computes a value.

.. centered:: **Legality Rules**

.. _tu-expressions-01:

1. An expression shall be side-effect free.
   [Strictly speaking, this "rule" is a consequence of other rules,
   most notably the rule that a function cannot have outputs other
   than its result.]

.. _tu-expressions-02:

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

    * an indexing expression of an indexed_component or the discrete_range
      of a slice in an object renaming declaration which renames
      part of that index or slice (see :ref:`object_renaming_declarations`);

    * a generic actual parameter corresponding to a generic formal object
      having mode **in** (see :ref:`generic_instantiation`);

    * the declaration and body of a user-defined equality operation on a
      record type (see :ref:`overloading_of_operators`).

      [This avoids the case where such a record type is a component of another
      composite type, whose predefined equality operation now depends on
      variables through the primitive equality operation on its component.]

.. _etu-expressions:

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

.. _update-expressions:

Update Expressions
~~~~~~~~~~~~~~~~~~

The Update attribute provides a way of overwriting specified
components of a copy of a given composite value.

For a prefix ``X``
that denotes an object of a nonlimited record type or record extension
``T``, the attribute

::

     X'Update ( record_component_association_list )

is defined and yields a value of type ``T`` and is a *record update
expression*.

For a prefix ``X`` that denotes an object of a nonlimited one
dimensional array type ``T``, the attribute

::

     X'Update ( array_component_association {, array_component_association} )

is defined and yields a value of type ``T`` and is an *array update
expression*.

For a prefix ``X`` that denotes an object of a nonlimited
multidimensional array type ``T``, the attribute

::

    X'Update ( multidimensional_array_component_association
            {, multidimensional_array_component_association} )

is defined and yields a value of type ``T`` and is a
*multi-dimensional array update*.  Where
``multidimensional_array_component_association`` has the following
syntax:

.. centered:: **Syntax**

::

  multidimensional_array_component_association ::=
    index_expression_list_list => expression
  index_expression_list_list ::=
    index_expression_list { | index_expression_list }
  index_expression_list ::=
    ( expression {, expression} )

.. centered:: **Legality Rules**

.. _tu-update_expressions-01:

1. The box symbol, <>, may not appear in any ``expression`` appearing
   in an *update expression*.

.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-02:

2. In all cases (i.e., whether ``T`` is a record type, a record
   extension type, or an array type - see below), evaluation of
   ``X'Update`` begins with the creation of an anonymous object of
   type ``T`` which is initialized to the value of ``X`` in the same
   way as for an occurrence of ``X'Old`` (except that the object is
   constrained by its initial value but not constant).

.. _tu-update_expressions-03:

3. Next, components of this object are updated as described in the
   following subsections. The attribute reference then denotes a
   constant view of this updated object. The master and accessibility
   level of this object are defined as for the anonymous object of an
   aggregate.

.. _tu-update_expressions-04:

4. The assignments to components of the result object described in the
   following subsections are assignment operations and include
   performance of any checks associated with evaluation of the target
   component name or with implicit conversion of the source value to
   the component subtype.

.. _etu-update_expressions:


Record Update Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^

For a record update expression of type ``T`` the following are
required.

.. centered:: **Legality Rules**

.. _tu-update_expressions-05:

5. The ``record_component_association_list`` shall have one or more
   ``record_component_associations``, each of which shall have a
   non-**others** ``component_choice_list`` and an expression.

.. _tu-update_expressions-06:

6. Each ``selector_name`` of each ``record_component_name`` shall denote a
   distinct non discriminant component of ``T``.

.. _tu-update_expressions-07:

7. Each ``record_component_association``'s associated components shall
   all be of the same type. The expected type and applicable index
   constraint of the expression is defined as for a
   ``record_component_association`` occurring within a record
   aggregate.

.. _tu-update_expressions-08:

8. Each selector of all ``component_choice_lists`` of a record
   update expression shall denote a distinct component.

.. _etu-record_update_expressions-lr:


.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-09:

9. For each component for which an expression is provided, the
   expression value is assigned to the corresponding component of the
   result object. The order in which the components are updated is
   unspecified.

.. _etu-record_update_expressions-ds:

[Components in a record update expression must be distinct.  The following is illegal

::

  Some_Record'Update
    (Field_1 => ... ,
     Field_2 => ... ,
     Field_1 => ... ); -- illegal; components not distinct

because the order of component updates is unspecified.]

Array Update Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^

For an array update expression of type ``T`` the following are
required.

.. centered:: **Legality Rules**

.. _tu-update_expressions-10:

10. Each ``array_component_association`` of the attribute reference
    shall have one or more ``array_component_associations``, each of
    which shall have an expression.

.. _tu-update_expressions-11:

11. The expected type and applicable index constraint of the
    expression is defined as for an ``array_component_association``
    occurring within an array aggregate of type ``T``. The expected
    type for each ``discrete_choice`` is the index type of ``T``.

.. _tu-update_expressions-12:

12. The reserved word **others** shall not occur as a
    ``discrete_choice`` of an ``array_component_association`` of the
    ``attribute_reference``.

.. _etu-array_update_expressions-lr:

.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-13:

13. The discrete choices and array component expressions are
    evaluated. Each array component expression is evaluated once for
    each associated component, as for an array aggregate. For each
    such associated component of the result object, the expression
    value is assigned to the component.

.. _tu-update_expressions-14:

14. Evaluations and updates are performed in the order in which the
    ``array_component_associations`` are given; within a single
    ``array_component_association``, in the order of the
    ``discrete_choice_list``; and within the range of a single
    ``discrete_choice``, in ascending order.

.. _tu-update_expressions-14.1:

[Note: the ``Update`` attribute for an array object allows multiple
assignments to the same component, as in either

::

  Some_Array'Update (1 .. 10 => True, 5 => False)

or

::

  Some_Array'Update (Param_1'Range => True, Param_2'Range => False)
  -- ok even if the two ranges overlap]

.. _etu-array_update_expressions-ds:

Multi-dimensional Array Update Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

For a multi-dimensional array update expression of type ``T`` the
following are required.

.. centered:: **Legality Rules**

.. _tu-update_expressions-15:

15. The expected type and applicable index constraint of the
    expression of a ``multidimensional_array_component_association``
    are defined as for the expression of an
    ``array_component_association`` occurring within an array
    aggregate of type ``T``.

.. _tu-update_expressions-16:

16. The length of each ``index_expression_list`` shall equal the
    dimensionality of ``T``. The expected type for each expression in
    an ``index_expression_list`` is the corresponding index type of
    ``T``.

.. _etu-multi_dimensional_array_update_expressions-lr:

.. centered:: **Dynamic Semantics**

.. _tu-multi_dimensional_array_update_expressions-17:

17. For each ``multidimensional_array_component`` association (in the
    order in which they are given) and for each
    ``index_expression_list`` (in the order in which they are given),
    the index values of the ``index_expression_list`` and the
    expression are evaluated (in unspecified order) and the expression
    value is assigned to the component of the result object indexed by
    the given index values. Each array component expression is
    evaluated once for each associated ``index_expression_list``.

.. _etu-multi_dimensional_array_update_expressions-ds:

.. centered:: **Examples**

.. literalinclude:: ../../../testsuite/gnatprove/tests/RM_Examples/update_examples.ads
   :language: ada
   :linenos:

Operators and Expression Evaluation
-----------------------------------

Ada grants implementations the freedom to reassociate a sequence
of predefined operators of the same precedence level even if this
changes the behavior of the program with respect to intermediate
overflow (see Ada 2012 RM 4.5). |SPARK| assumes that an implementation
does not take advantage of this permission; in particular,
a proof of the absence of intermediate overflow in this situation
may depend on this assumption.

A |SPARK| tool is permitted to provide a warning where operators may
be re-associated by a compiler.

[The GNAT Ada 2012 compiler does not take advantage of this permission.
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

.. _tu-allocators-01:

1. The designated type of the type of an uninitialized allocator
   shall define full default initialization.

.. _tu-allocators-02:

2. Evaluation of an allocator is subject to the same restrictions as calling a
   volatile function (e.g., an allocator is not allowed within a non-volatile
   function). [If it seems helpful, an allocator may be thought of as being
   like a call to a volatile function which returns the access value
   designating the allocated object.]

.. _tu-allocators-03:

3. The type of an allocator shall not be anonymous.

.. _etu-allocators:

Static Expressions and Static Subtypes
--------------------------------------

No extensions or restrictions.
