Names and Expressions
=====================

.. todo:: The text for *New Attributes* has been copied directly from the initial langauge
    design document as prepared by Johannes. It needs to be tided up
    into LRM format.  It was headed Richer Expressions but describes
    attributes.  I am not sure this is the right chapter for these?

We denote by *assertion expression* an expression that appears inside an
assertion, which can be a pragma Assert, a precondition or postcondition, a
type invariant or predicate, or other assertions introduced in |SPARK|.

Restrictions
------------

A name that denotes an entity is in |SPARK| if and only if the entity is in
|SPARK|. Neither ``explicit_dereference`` nor ``implicit_dereference`` are in
|SPARK|.

Attribute ``Access`` is not in |SPARK|. As they are based on access
discriminants, user-defined references and user-defined indexing are not in
|SPARK|.

The literal **null** is not allowed in |SPARK|.

Outside of assertion expressions, an aggregate is in |SPARK| only if its type
is in |SPARK| and it is side-effect free. Inside assertion expressions,
aggregates in |SPARK| must additionally be fully defined. An aggregate which
leaves subcomponents uninitialized is not in |SPARK| if it appears inside an
assertion expression.

An expression is in |SPARK| only if its type is in |SPARK| and it is
side-effect free.

The use of allocators is not allowed in |SPARK|.

The Update attribute
--------------------

The Update attribute provides a way of overwriting specified components
of a copy of a given composite value.
For a prefix X that denotes an object of a nonlimited record type or
record extension T, the attribute

   X'Update ( record_component_association_list )

is defined and yields a value of type T. The
record_component_association_list shall have
one or more record_component_associations, each of which
shall have a component_choice_list and an expression.

Each Selector_Name of each record_component_name shall denote a
distinct non-discriminant component of T.
Each record_component_association's associated components shall all
be of the same type. The expected type and applicable index
constraint of the expression is defined as for a
record_component_association occurring within a record aggregate.

In all cases (i.e., whether T is a record type, a record extension type,
or an array type - see below), evaluation of X'Update
begins with the creation of an anonymous object of
type T which is initialized to the value of X in the same way as for an
occurrence of X'Old (except that the object is constrained
by its initial value but not constant). Next, components of this object
are updated as described below. The attribute reference then denotes a
constant view of this updated object. The master and
accessibility level of this object are defined as for the anonymous
object of an aggregate. The assignments to components of the
result object described below are assignment operations and include
performance of any checks associated with evaluation of the target
component name or with implicit conversion of the source value to
the component subtype.

If T is a record type or record extension then the component updating
referenced above proceeds as follows. For each component for which an
expression is provided, the expression value is assigned to the
corresponding component of the result object. The order in which the
components are updated is unspecified.

For a prefix X that denotes an object of a nonlimited one
dimensional array type T, the attribute

::

   X'Update ( array_component_association {, array_component_association} )

is defined and yields a value of type T.

Each array_component_association of the attribute reference shall
have one or more array_component_associations, each of which
shall have an expression. The expected type and applicable index
constraint of the expression is defined as for an
array_component_association occurring within an array aggregate of
type T. The expected type for each discrete_choice is the index
type of T.

For a prefix X that denotes an object of a nonlimited
multidimensional array type T, the attribute

::

  X'Update ( multidimensional_array_component_association
             {, multidimensional_array_component_association} )

is defined with associated syntax

::

  multidimensional_array_component_association ::=
    index_expression_list_list => expression
  index_expression_list_list ::=
    index_expression_list { | index_expression_list }
  index_expression_list ::=
    ( expression {, expression} ) 

and yields an object of type T.

The expected type and applicable index constraint of the expression
of a multidimensional_array_component_association are defined as for
the expression of an array_component_association occurring within an
array aggregate of type T.
The length of each index_expression_list shall equal the
dimensionality of T. The expected type for each expression in an
index_expression_list is the corresponding index type of T.
   
If T is one-dimensional type then the component updating referenced
above proceeds as follows. The discrete choices and array
component expressions are evaluated. Each array component
expression is evaluated once for each associated component, as for
an array aggregate. For each such associated component of the result
object, the expression value is assigned to the component.
Evaluations and updates are performed in the order in which the
array_component_associations are given; within a single
array_component_association, in the order of the
discrete_choice_list; and within the range of a single
discrete_choice, in ascending order.

If T is a multidimensional type then the component updating referenced
above proceeds as follows. For each
multidimensional_array_component association (in the order in which
they are given) and for each index_expression_list (in the order
in which they are given), the index values of the index_expression_list
and the expression are evaluated (in unspecified order)
and the expression value is assigned to the component of the result
object indexed by the given index values. Each array component expression
is evaluated once for each associated index_expression_list.
  
Note: the Update attribute for an array object allows multiple
assignments to the same component, as in either

::

  Some_Array'Update (1 .. 10 => True, 5 => False)

or

::

  Some_Array'Update (Param_1'Range => True, Param_2'Range => False)
  -- ok even if the two ranges overlap

This is different than the Update attribute of a record 

::

  Some_Record'Update
    (Field_1 => ... ,
     Field_2 => ... ,
     Field_1 => ... ); -- illegal; components not distinct

for which the order of component updates is unspecified.

Legality rules
^^^^^^^^^^^^^^

Some constructs which would unconditionally raise an exception at
runtime in Ada are instead, if this can be determined at compile time,
rejected as illegal in SPARK. In particular, if the prefix of a
record component selection is known statically to be constrained so
that the selected component is not present, then the component
selection (which, in Ada, would raise Constraint_Error if it were
to be evaluated) is illegal.

.. todo:: list all such illegal-due-to-inevitable-exception constructs


Semantics
^^^^^^^^^

The expression ``Name'Valid_Scalars`` is a boolean expression that evaluates to
``True`` whenever all scalar components or subcomponents of ``Name`` have
values allowed by their type.

.. todo:: Valid_Scalars is already in GNAT RM. How do we want to handle that?
