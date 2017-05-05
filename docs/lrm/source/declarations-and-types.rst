Declarations and Types
======================

No extensions or restrictions.

.. _declarations:

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*. If the initial declaration
of an entity (e.g., a subprogram, a private type, or a deferred
constant) requires a completion, it is possible that the initial declaration
might be in |SPARK| (and therefore can be referenced in |SPARK| code)
even if the completion is not in |SPARK|. [This distinction between views
is much less important in "pure" |SPARK| than in the case where SPARK_Mode is
used (as described in the SPARK Toolset User's Guide) to allow mixing
of |SPARK| and non-|SPARK| code.]

A type is said to *define full default initialization* if it is

  * a scalar type with a specified Default_Value; or

  * an array-of-scalar type with a specified Default_Component_Value; or

  * an array type whose element type defines default initialization; or

  * a record type, type extension, or protected type each of whose
    ``component_declarations`` either includes a ``default_expression`` or
    has a type which defines full default initialization and, in the case of
    a type extension, is an extension of a type which defines full default
    initialization; or

  * a task type; or

  * a private type whose Default_Initial_Condition aspect is specified to be a
    *Boolean_*\ ``expression``.

[The discriminants of a discriminated type play no role in determining
whether the type defines full default initialization.]


Types and Subtypes
------------------

No extensions or restrictions.


Type Declarations
~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-sf-type_declarations-01:

1. Named access-to-constant types are permitted in |SPARK|.  All other access
   type declarations are not permitted in |SPARK|, as well as all forms of
   anonymous access types.

.. _etu-type_declarations:

.. _subtype_declarations:

Subtype Declarations
~~~~~~~~~~~~~~~~~~~~

A ``constraint`` in |SPARK| cannot be defined using variable
expressions except when it is the ``range`` of a
``loop_parameter_specification``. Dynamic subtypes are permitted but
they must be defined using constants whose values may be derived from
expressions containing variables. Note that a formal parameter of a
subprogram of mode **in** is a constant and may be used in defining a
constraint. This restriction gives an explicit constant which can be
referenced in analysis and proof.

An expression with a *variable input* reads a variable or calls a
function which (directly or indirectly) reads a variable.

.. centered:: **Legality Rules**

.. _tu-subtype_declarations-01:

1. [A ``constraint``, excluding the ``range`` of a
   ``loop_parameter_specification``, shall not be defined using an
   expression with a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-subtype_declarations-lr:


Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

.. _subtype_predicates:

Subtype Predicates
~~~~~~~~~~~~~~~~~~

Static predicates are in |SPARK|. Dynamic predicates are also in
|SPARK|, but are subject to some restrictions.

.. centered:: **Legality Rules**

.. _tu-sf-subtype_predicates-01:

1. [A Dynamic_Predicate expression shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-subtype_predicates-01:

.. _tu-sf-subtype_predicates-02:

2. If a Dynamic_Predicate applies to the subtype of a composite object,
   then a verification condition is generated to ensure that the object
   satisfies its predicate immediately after any subcomponent or slice
   of the given object is either

  * the target of an assignment statement or;

  * an actual parameter of mode **out** or **in out** in a call.

  [These verification conditions do not correspond to any run-time
  check. Roughly speaking, if object X is of subtype S, then verification
  conditions are generated as if an implicitly generated

     pragma Assert (X in S);

  were present immediately after any assignment statement or call which
  updates a subcomponent (or slice) of X.]

  [No such proof obligations are generated for assignments
  to subcomponents of the result object of an aggregate,
  an extension aggregate, or an update expression (see section
  :ref:`update-expressions`).
  These are assignment operations but not assignment statements.]

.. _etu-subtype_predicates-02:


Objects and Named Numbers
-------------------------

.. _object-declarations:

Object Declarations
~~~~~~~~~~~~~~~~~~~

The Boolean aspect Constant_After_Elaboration may be specified as part of
the declaration of a library level variable.
If the aspect is directly specified, the aspect_definition, if any,
shall be a static [Boolean] expression. [As with most Boolean-valued
aspects,] the aspect defaults to False if unspecified and to True if
it is specified without an aspect_definition.

A variable whose Constant_After_Elaboration aspect is True, or any part
thereof, is said to be *constant after elaboration*.
[The Constant_After_Elaboration aspect indicates that the variable will not
be modified after execution of the main subprogram begins
(see section :ref:`tasks-and-synchronization`).]

A stand-alone constant is a *constant with variable inputs* if its
initialization expression depends on:

  * A variable or parameter; or

  * Another *constant with variable inputs*

Otherwise, a stand-alone constant is a *constant without variable inputs*.

.. centered:: **Verification Rules**

.. _tu-object_declarations-01:

1. Constants without variable inputs shall not be denoted in Global,
   Depends, Initializes or Refined_State aspect specifications.
   [Two elaborations of such a constant declaration will always
   yield equal initialization expression values.]

.. _etu-object_declarations-vr:

.. centered:: **Examples**

.. code-block:: ada

   A : constant Integer := 12;
   --  No variable inputs

   B : constant Integer := F (12, A);
   --  No variable inputs if F is a function without global inputs (although
   --  it could have global proof inputs)

   C : constant Integer := Param + Var;
   --  Constant with variable inputs


Number Declarations
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Derived Types and Classes
-------------------------

The following rules apply to derived types in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-derived_types-01:

1. A private type that is not visibly tagged but whose full view is tagged
   cannot be derived.

[The rationale for this rule is that, otherwise, given that visible operations
on this type cannot have class-wide preconditions and postconditions, it is
impossible to check the verification rules associated to overridding operations
on the derived type.]

.. _etu-derived_types:

Scalar Types
------------

The Ada RM states that, in the case of a fixed point type declaration,
"The base range of the type does not necessarily include the specified
bounds themselves". A fixed point type for which this inclusion does
not hold is not in |SPARK|.

For example, given

.. code-block:: ada

   type T is delta 1.0 range -(2.0 ** 31) .. (2.0 ** 31);

it might be the case that (2.0 ** 31) is greater
than T'Base'Last. If this is the case, then the type T is not in |SPARK|.

[This rule applies even in the case where the bounds
specified in the ``real_range_specification`` of an
``ordinary_fixed_point_definition`` define a null range.]

Array Types
-----------

No extensions or restrictions.

.. _discriminants:

Discriminants
-------------

The following rules apply to discriminants in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-discriminants-01:

1. The type of a ``discriminant_specification`` shall be discrete.

.. _tu-discriminants-02:

2. A ``discriminant_specification`` shall not occur as part of a
   derived type declaration.

.. _tu-discriminants-03:

3. [The ``default_expression`` of a ``discriminant_specification``
   shall not have a variable input;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-discriminants:

.. _record_types:

Record Types
------------

Default initialization expressions must not have variable inputs in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-record_types-01:

1. If at least one nondiscriminant component (either explicitly
   declared or inherited) of a record type or type extension either is
   of a type which defines full default initialization or is declared
   by a ``component_declaration`` which includes a
   ``default_expression``, and if that component's type has at least
   one elementary nondiscriminant part, then the record type or type
   extension shall define full default initialization.

   [The enforcement of this rule may require looking at the
   ``full_type_declaration`` of a ``private_type`` declaration if the
   private type's Default_Initial_Condition aspect is not specified.]

   [In the unusual case of a nondiscriminant component which has no
   nondiscriminant scalar parts (e.g., an array of null records),
   the preceding "at least one elementary" wording means that the component
   is ignored for purposes of this rule.]

.. _tu-record_types-02:

2. [The ``default_expression`` of a ``component_declaration`` shall not
   have any variable inputs, nor shall it contain a name denoting
   the current instance of the enclosing type;
   see :ref:`expressions` for the statement of this rule.]

.. _etu-record_types:

[The rules in this section apply to any ``component_declaration``; this
includes the case of a ``component_declaration`` which is a
``protected_element_declaration``. In other words, these rules also apply to
components of a protected type.]

Tagged Types and Type Extensions
--------------------------------

.. centered:: **Legality Rules**

.. _tu-tagged_types-01:

1.  No construct shall introduce a semantic dependence on the Ada
    language defined package Ada.Tags.
    [See Ada RM 10.1.1 for the definition of semantic dependence.
    This rule implies, among other things, that any use of the Tag attribute
    is not in |SPARK|.]

.. _tu-tagged_types-02:

2.  The identifier External_Tag shall not be used as an
    ``attribute_designator``.

.. _etu-tagged_types:


Type Extensions
~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-type_extensions-01:

1.  A type extension shall not be declared within a
    subprogram body, block statement, or generic body which does not
    also enclose the declaration of each of its ancestor types.

.. _etu-type_extensions:


Dispatching Operations of Tagged Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Abstract Types and Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Interface Types
~~~~~~~~~~~~~~~

No extensions or restrictions.

Access Types
------------

Access types allow the creation of aliased data structures and objects, which
notably complicate the specification and verification of a program's
behavior. Therefore, the following rules are applied in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-access_types-01:

1. All forms of access type and parameter declarations are prohibited.
   [This follows from the rule forbidding use of the Ada reserved
   word **access**.]

.. _tu-access_types-02:

2. The attribute 'Access shall not be denoted.

.. _etu-access_types:


Declarative Parts
-----------------

No extensions or restrictions.
