Names and Expressions
=====================

The term *assertion expression* denotes an expression that appears inside an
assertion, which can be a pragma Assert, a precondition or postcondition, a
type invariant or (subtype) predicate, or other assertions introduced in |SPARK|.

Names
-----

.. centered:: **Legality Rules**

.. _tu-names-01:

1. A name that denotes an entity is in |SPARK| if and only if the
   entity is in |SPARK|.

.. _tu-names-02:

2. Neither ``explicit_dereference`` nor ``implicit_dereference`` are
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
are exclusions for instance X'Access, as access types are not
supported.  For a full list of attributes supported by |SPARK| see
:ref:`language_defined_attributes`.

A |SPARK| implementation is permitted to support other attributes
which are not Ada or |SPARK| language defined attributes and these
should be documented in the User Guide for the tool.


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

.. centered:: **Legality Rules**

.. _tu-literals-01:

1. The literal **null** representing an access value is not allowed.

.. _etu-literals:

Aggregates
----------

.. centered:: **Legality Rules**

.. _tu-aggregates-01:

1. The box symbol, <>, may only be used in an aggregate if the type(s)
   of the corresponding component(s) define full default initialization.

.. _etu-aggregates:

[The box symbol cannot be used in an aggregate to produce an uninitialized
scalar value or a composite value having an uninitialized scalar value as a
subcomponent.]

Expressions
-----------

An expression is said to be *side-effect free* if the evaluation of the
expression does not update any object.  The evaluation of an expression
free from side-effects only retrieves or computes a value.

.. centered:: **Legality Rules**

.. _tu-expressions-01:

1. An expression is in |SPARK| only if its type is in |SPARK| and the
   expression is side-effect free.

.. _tu-expressions-02:

2. An expression (or range) in |SPARK| occurring in certain contexts
   (listed below) shall not have a variable input.  This means that
   such an expression shall not read a variable, nor shall it call a
   function which (directly or indirectly) reads a variable.  These
   contexts include:

    * a constraint excluding the range of a loop parameter
      specification where variables may be used in the expressions
      defining the range (see :ref:`subtype_declarations`);

    * the default_expression of a component declaration (see
      :ref:`record_types`);

    * the default_expression of a discriminant_specification
      (see :ref:`discriminants`);

    * a Dynamic_Predicate aspect specification;

    * an indexing expresssion of an indexed_component or the discrete_range
      of a slice in an object renaming declaration which renames
      part of that index or slice.

.. _etu-expressions:

[An expression in one of these contexts may read a constant
which is initialized with the value of a variable.]

[The Dynamic_Predicate rule is redundant because no use of the
Dynamic_Predicate is currently in |SPARK|. This rule is added
in anticipation of the possible relaxation of that restriction.]

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
expression*..

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

is defined and yields an object of type ``T`` and is a
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

.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-01:

1. In all cases (i.e., whether ``T`` is a record type, a record
   extension type, or an array type - see below), evaluation of
   ``X'Update`` begins with the creation of an anonymous object of
   type ``T`` which is initialized to the value of ``X`` in the same
   way as for an occurrence of ``X'Old`` (except that the object is
   constrained by its initial value but not constant).

.. _tu-update_expressions-02:

2. Next, components of this object are updated as described in the
   following subsections. The attribute reference then denotes a
   constant view of this updated object. The master and accessibility
   level of this object are defined as for the anonymous object of an
   aggregate.

.. _tu-update_expressions-03:

3. The assignments to components of the result object described in the
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

.. _tu-update_expressions-04:

4. The ``record_component_association_list`` shall have one or more
   ``record_component_associations``, each of which shall have a
   non-**others** ``component_choice_list`` and an expression.

.. _tu-update_expressions-05:

5. Each ``selector_name`` of each ``record_component_name`` shall denote a
   distinct non discriminant component of ``T``.

.. _tu-update_expressions-06:

6. Each ``record_component_association``'s associated components shall
   all be of the same type. The expected type and applicable index
   constraint of the expression is defined as for a
   ``record_component_association`` occurring within a record
   aggregate.

.. _tu-update_expressions-07:

7. Each selector of all ``component_choice_lists`` of a record
   update expression shall denote a distinct component.

.. _etu-record_update_expressions-lr:


.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-08:

8. For each component for which an expression is provided, the
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

because  the order of component updates is unspecified.]

Array Update Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^

For an array update expression of type ``T`` the following are
required.

.. centered:: **Legality Rules**

.. _tu-update_expressions-09:

9. Each ``array_component_association`` of the attribute reference
   shall have one or more ``array_component_associations``, each of
   which shall have an expression.

.. _tu-update_expressions-10:

10. The expected type and applicable index constraint of the
    expression is defined as for an ``array_component_association``
    occurring within an array aggregate of type ``T``. The expected
    type for each ``discrete_choice`` is the index type of ``T``.

.. _tu-update_expressions-11:

11. The reserved word **others** shall not occur as a
    ``discrete_choice`` of an ``array_component_association`` of the
    ``attribute_reference``.

.. _etu-array_update_expressions-lr:

.. centered:: **Dynamic Semantics**

.. _tu-update_expressions-12:

12. The discrete choices and array component expressions are
    evaluated. Each array component expression is evaluated once for
    each associated component, as for an array aggregate. For each
    such associated component of the result object, the expression
    value is assigned to the component.

.. _tu-update_expressions-13:

13. Evaluations and updates are performed in the order in which the
    ``array_component_associations`` are given; within a single
    ``array_component_association``, in the order of the
    ``discrete_choice_list``; and within the range of a single
    ``discrete_choice``, in ascending order.

.. _tu-update_expressions-13.1:

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

.. _tu-update_expressions-14:

14. The expected type and applicable index constraint of the
    expression of a ``multidimensional_array_component_association``
    are defined as for the expression of an
    ``array_component_association`` occurring within an array
    aggregate of type ``T``.

.. _tu-update_expressions-15:

15. The length of each ``index_expression_list`` shall equal the
    dimensionality of ``T``. The expected type for each expression in
    an ``index_expression_list`` is the corresponding index type of
    ``T``.

.. _etu-multi_dimensional_array_update_expressions-lr:

.. centered:: **Dynamic Semantics**

.. _tu-multi_dimensional_array_update_expressions-16:

16. For each ``multidimensional_array_component`` association (in the
    order in which they are given) and for each
    ``index_expression_list`` (in the order in which they are given),
    the index values of the ``index_expression_list`` and the
    expression are evaluated (in unspecified order) and the expression
    value is assigned to the component of the result object indexed by
    the given index values. Each array component expression is
    evaluated once for each associated ``index_expression_list``.

.. _etu-multi_dimensional_array_update_expressions-ds:

.. centered:: **Examples**

.. code-block:: ada

   package Update_Examples
     with SPARK_Mode
   is
      type Rec is record
         X, Y : Integer;
      end record;

      type Arr is array (1 .. 3) of Integer;

      type Arr_2D is array (1 .. 3, 1 .. 3) of Integer;

      type Nested_Rec is record
         A : Integer;
         B : Rec;
         C : Arr;
         D : Arr_2D;
      end record;

      type Nested_Arr is array (1 .. 3) of Nested_Rec;

      -- Simple record update
      procedure P1 (R : in out Rec)
        with Post => R = R'Old'Update (X => 1);
      -- this is equivalent to:
      --   R = (X => 1,
      --        Y => R'Old.Y)

      -- Simple 1D array update
      procedure P2 (A : in out Arr)
        with Post => A = A'Old'Update (1 => 2);
      -- this is equivalent to:
      --   A = (1 => 2,
      --        2 => A'Old (2),
      --        3 => A'Old (3));

      -- 2D array update
      procedure P3 (A2D : in out Arr_2D)
        with Post => A2D = A2D'Old'Update ((1, 1) => 1,
                                           (2, 2) => 2,
                                           (3, 3) => 3);
      -- this is equivalent to:
      --   A2D = (1 => (1 => 1,
      --                2 => A2D'Old (1, 2),
      --                3 => A2D'Old (1, 3)),
      --          2 => (2 => 2,
      --                1 => A2D'Old (2, 1),
      --                3 => A2D'Old (2, 3)),
      --          3 => (3 => 3,
      --                1 => A2D'Old (3, 1),
      --                2 => A2D'Old (3, 2)));

      -- Nested record update
      procedure P4 (NR : in out Nested_Rec)
        with Post => NR = NR'Old'Update (A => 1,
                                         B => NR'Old.B'Update (X => 1),
                                         C => NR'Old.C'Update (1 => 5));
      -- this is equivalent to:
      --   NR = (A => 1,
      --         B.X => 1,
      --         B.Y => NR'Old.B.Y,
      --         C (1) => 5,
      --         C (2) => NR'Old.C (2),
      --         C (3) => NR'Old.C (3),
      --         D => NR'Old.D)

      -- Nested array update
      procedure P5 (NA : in out Nested_Arr)
        with Post =>
          NA = NA'Old'Update (1 => NA'Old (1)'Update
                                     (A => 1,
                                      D => NA'Old (1).D'Update ((2, 2) => 0)),
                              2 => NA'Old (2)'Update
                                     (B => NA'Old (2).B'Update (X => 2)),
                              3 => NA'Old (3)'Update
                                     (C => NA'Old (3).C'Update (1 => 5)));
      -- this is equivalent to:
      --   NA = (1 => (A => 1,
      --               B => NA'Old (1).B,
      --               C => NA'Old (1).C,
      --               D => NA'Old (1).D),
      --         2 => (B.X => 2,
      --               B.Y => NA'Old (2).B.Y,
      --               A => NA'Old (2).A,
      --               C => NA'Old (2).C,
      --               D => NA'Old (2).D),
      --         3 => (C => (1 => 5,
      --                     2 => NA'Old (3).C (2),
      --                     3 => NA'Old (3).C (3)),
      --               A => NA'Old (3).A,
      --               B => NA'Old (3).B,
      --               D => NA'Old (3).D));

   end Update_Examples;

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

1. The use of allocators is not permitted.

.. _etu-allocators:

Static Expressions and Static Subtypes
--------------------------------------

No extensions or restrictions.
