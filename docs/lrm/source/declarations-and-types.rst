Declarations and Types
======================

|SPARK| does not add any declarations or types to Ada 2012, but it restricts
their usage.

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*.

A type is said to *define full default initialization* if it is

  * a scalar type with a specified Default_Value; or

  * an array-of-scalar type with a specified Default_Component_Value; or

  * an array type whose element type defines default initialization; or

  * a record type or type extension each of whose ``component_declarations``
    either includes a ``default_expression`` or has a type which defines full
    default initialization and, in the case of a type extension, is
    an extension of a type which defines full default initialization.

[The discriminants of a discriminated type play no role in determining
whether the type defines full default initialization.]


Types and Subtypes
------------------

.. centered:: **Legality Rules**

.. _tu-types_and_subtypes-01:

1. The view of an entity introduced by a ``private_type_declaration``
   is in |SPARK| if the types of any visible discriminants are in
   |SPARK|, even if the entity declared by the corresponding
   ``full_type_declaration`` is not in |SPARK|.

.. _tu-types_and_subtypes-02:

2. For a type or subtype to be in |SPARK|, all predicate
   specifications that apply to the (sub)type must be in |SPARK|.
   Notwithstanding any rule to the contrary, a (sub)type is never in
   |SPARK| if its applicable predicate is not in |SPARK|.

.. _tu-types_and_subtypes-03:

3. Constants, including those implicitly declared through a
   non-preelaborable subtype declaration shall not be denoted in
   Global, Depends, Initializes or Refined_State aspects.  [This means
   that non-preelaborable subtypes are not taken into account in
   determining and checking dependency relations.]

.. _etu-types_and_subtypes:

.. todo:: Lift restriction that non-preelaborable subtypes are not subject
          to flow analysis. To be completed in a post-Release 1 version of this document.

Type Declarations
~~~~~~~~~~~~~~~~~

.. centered:: **Legality Rules**

.. _tu-type_declarations-01:

1. The following type declarations are not permitted in |SPARK|

   * ``task_type_declaration``,
   * ``protected_type_declaration``, 
   * ``private_extension_declaration``, 
   * ``interface_type_definition``, and
   * ``access_type_definition``.

.. _etu-type_declarations:

[``Task_type_declarations`` and ``protected_type_declarations`` will
be included when |SPARK| is extended to cover some of the Ada tasking
features. ``Private_extension_declarations`` and
``interface_type_definitions`` may be included when |SPARK| is
extended to support tagged types.]

.. _subtype_declarations:

Subtype Declarations
~~~~~~~~~~~~~~~~~~~~

A ``constraint`` in |SPARK| cannot be defined using variable
expressions except when it is the ``range`` of a
``loop_parameter_specification``.  Dynamic subtypes are permitted but
they must be defined using constants whose values may be derived from
expressions containing variables.  Note that a formal parameter of a
subprogram of mode **in** is a constant and may be used in defining a
constraint. This restriction gives an explicit constant which can be
referenced in analysis and proof.

An expression with a *variable input* reads a variable or calls a
function which calls (directly or indirectly) reads a variable.

.. centered:: **Legality Rules**

.. _tu-subtype_declarations-01:

1. A ``constraint``, excluding the ``range`` of a
   ``loop_parameter_specification``, shall not be defined using an
   expression with a variable input.

.. _etu-subtype_declarations:
 
 
Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Subtype Predicates
~~~~~~~~~~~~~~~~~~

Static predicates are in |SPARK| but dynamic predicates are not in
|SPARK|.

.. centered:: **Legality Rules**

.. _tu-subtype_predicates-01:

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

.. centered:: **Legality Rules**

.. _tu-object_declarations-01:

1. The entity declared by an ``object_declaration`` is in |SPARK| if
   its declaration does not contain the reserved word **aliased**, its
   type is in |SPARK|, and its *initialization_*\ ``expression``, if
   any, is in |SPARK|.

.. _tu-object_declarations-02:

2. Constants including those that are not preelaborable shall not be
   denoted in Global, Depends, Initializes or Refined_State
   aspects. [This means that non-preelaborable constants are not taken
   into account in determining and checking dependency relations.]

.. _etu-object_declarations:

.. todo:: Lift restriction that non-preelaborable constants are not subject
          to flow analysis. To be completed in a post-Release 1 version of this document.

Number Declarations
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Derived Types and Classes
-------------------------

.. centered:: **Legality Rules**

.. _tu-derived_types_and_classes-01:

1. An entity declared by a ``derived_type`` declaration is in |SPARK|
   if its parent type is in |SPARK|, and if the declaration contains
   an ``interface_list`` or a ``record_part`` these must also contain
   entities that are in |SPARK|.

.. _etu-derived_types_and_classes:

Scalar Types
------------

No extensions or restrictions.


Array Types
-----------

.. centered:: **Legality Rules**

.. _tu-array_types-01:

1. An entity declared by a ``array_type_definition`` is in |SPARK| if its
   components are in |SPARK| and default initialization is in |SPARK|.

.. _etu-array_types:

.. _discriminants:

Discriminants
-------------

The following rules apply to discriminants in |SPARK|.

.. centered:: **Legality Rules**

.. _tu-discriminants-01:

1. The type of a ``discriminant_specification`` shall be discrete.

.. _tu-discriminants-02:

2. A ``discriminant_specification`` shall not occur as part of a
   derived type declaration whose parent type is discriminated. [In
   other words, inherited discriminants shall not be hidden.]

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
   have any variable inputs.

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

|SPARK| tagged types and type extensions are not supported
nor is the use of the 'Class attribute.

.. centered:: **Legality Rules**

.. _tu-tagged_types_and_type_extensions-01:

1. A record or private type declaration shall not contain the reserved
   word **tagged**.

.. _tu-tagged_types_and_type_extensions-02:

2. The attribute 'Class shall not be denoted.

.. _etu-tagged_types_and_type_extensions:

.. todo:: Add tagged types, type extensions and 'Class attribute to
     SPARK 2014. To be completed in a post-Release 1 version of this
     document.

Type Extensions
~~~~~~~~~~~~~~~

Tagged types are currently not in |SPARK|.

.. todo:: Tagged types are not in release 1.  The following rule
     applies to type extensions: A type extension declared within a
     subprogram body, block statement, or generic body which does not
     also enclose the declaration of each of its ancestor types is not
     in |SPARK|. To be completed in a post-Release 1 of theis document.


Dispatching Operations of Tagged Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tagged types are not currently in |SPARK|


Abstract Types and Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Tagged types are not currently in |SPARK|


Interface Types
~~~~~~~~~~~~~~~

Tagged types are not in |SPARK|.

.. todo:: Include interface types in SPARK 2014. To be completed in a post-Release 1
          version of this document.


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
