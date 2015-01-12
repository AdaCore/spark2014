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

  * a record type or type extension each of whose ``component_declarations``
    either includes a ``default_expression`` or has a type which defines full
    default initialization and, in the case of a type extension, is
    an extension of a type which defines full default initialization; or

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

1. The following type declarations are not permitted in |SPARK|

   * ``task_type_declaration``,
   * ``protected_type_declaration``, and
   * ``access_type_definition``.

.. _etu-type_declarations:

[``Task_type_declarations`` and ``protected_type_declarations`` will
be included when |SPARK| is extended to cover some of the Ada tasking
features.]

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

1. A ``constraint``, excluding the ``range`` of a
   ``loop_parameter_specification``, shall not be defined using an
   expression with a variable input.

.. _etu-subtype_declarations-lr:


Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Subtype Predicates
~~~~~~~~~~~~~~~~~~

Static predicates are in |SPARK| but dynamic predicates are not in
|SPARK|.

.. centered:: **Legality Rules**

.. _tu-sf-subtype_predicates-01:

1. A Dynamic_Predicate aspect shall not occur in an aspect specification.

.. _etu-subtype_predicates-01:

[Eventually |SPARK| may include uses of the Dynamic_Predicate aspect,
subject to the restriction that the predicate expression cannot take
any variables as inputs. This is needed to ensure that if a value
belonged to a subtype in the past, then the value will still belong
to the subtype in the future. Predicates for composite types might also
be restricted to disallow dependencies on non-discriminant components
(but allow dependencies on discriminants and array bounds) in order to
avoid cases where modifying a subcomponent can violate the subtype
predicate of an enclosing object.]

.. todo:: Add the Dynamic_Predicate aspect to SPARK 2014. To be completed
          in a post-Release 1 version of this document.

Objects and Named Numbers
-------------------------

Object Declarations
~~~~~~~~~~~~~~~~~~~

A constant is a *constant with variable inputs* if its initialization
expression depends on:

  * A variable or parameter

  * Another *constant with variable inputs*

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

No extensions or restrictions.

Scalar Types
------------

No extensions or restrictions.

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

3. The ``default_expression`` of a ``discriminant_specification``
   shall not have a variable input.

.. _etu-discriminants:

.. _record_types:

Record Types
------------

|SPARK| does not permit partial default initialization of record objects
and the default initialization expressions must not have variable inputs.

.. centered:: **Legality Rules**

.. _tu-record_types-01:

1. If at least one non-discriminant component (either explicitly
   declared or inherited) of a record type or type extension either is
   of a type which defines full default initialization or is declared
   by a ``component_declaration`` which includes a
   ``default_expression``, and if that component's type has at least
   one elementary non-discriminant part, then the record type or type
   extension shall define full default initialization.

.. _tu-record_types-02:

2. The ``default_expression`` of a ``component_declaration`` shall not
   have any variable inputs, nor shall it contain a name denoting
   the current instance of the enclosing type.

.. _etu-record_types:

[In the unusual case of a non-discriminant component which has no
non-discriminant scalar parts (e.g., an array of null records),
the preceding "at least one elementary" wording means that the component
is ignored for purposes of this rule.]

[The enforcement of this rule requires looking at the ``full_type_declaration``
of a ``private_type`` declaration. This is inconsistent with SPARK's usual
"everything you need to know should be in the specification" design.]

.. todo: Consider introducing some mechanism to optionally provide the needed
         information as part of the specification of a private type.

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

.. _tu-access_types-02:

2. The attribute 'Access shall not be denoted.

.. _etu-access_types:


Declarative Parts
-----------------

No extensions or restrictions.
