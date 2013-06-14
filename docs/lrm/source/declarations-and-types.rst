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

The view of an entity introduced by a ``private_type_declaration`` is in
|SPARK| if the types of any visible discriminants are in |SPARK|, even if the entity
declared by the corresponding ``full_type_declaration`` is not in |SPARK|.

For a type or subtype to be in |SPARK|, all predicate specifications that apply
to the (sub)type must be in |SPARK|.  Notwithstanding any rule to the contrary,
a (sub)type is never in |SPARK| if its applicable predicate is not in |SPARK|.

Subtypes that are not preelaborable are not subject to flow analysis.
[Users may write programs using such subtypes and those programs can be
subject to formal verification. However, flow analysis will ignore the use
of such a subtype and will instead raise a warning to indicate that its use has not
been analysed.]

.. todo:: Lift restriction that non-preelaborable subtypes are not subject
          to flow analysis. To be completed in a post-Release 1 version of this document.

Classification of Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No restrictions or extensions.

Subtype Predicates
~~~~~~~~~~~~~~~~~~

The Static_Predicate aspect is in |SPARK|.
The Dynamic_Predicate aspect is not in |SPARK|.

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

The entity declared by an ``object_declaration`` is
in |SPARK| if its declaration does not contain the reserved word **aliased**,
its type is in |SPARK|, and its *initialization_*\ ``expression``, if any, is in
|SPARK|.

Object Declarations
~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.

Number Declarations
~~~~~~~~~~~~~~~~~~~

Constants that are not preelaborable are not subject to flow analysis.
[Users may write programs using such constants and those programs can be
subject to formal verification. However, flow analysis will ignore the use
of such a constant and will instead raise a warning to indicate that its use has not
been analysed.]

.. todo:: Lift restriction that non-preelaborable constants are not subject
          to flow analysis. To be completed in a post-Release 1 version of this document.


Derived Types and Classes
-------------------------

An entity declared by a ``derived_type`` declaration is in |SPARK| if its
parent type is in |SPARK|, and if the declaration contains an ``interface_list``
or a ``record_part`` these must also contain entities that are in |SPARK|.

Scalar Types
------------

No extensions or restrictions.


Array Types
-----------

An entity declared by a ``array_type_definition`` is in |SPARK| if its
components are in |SPARK| and default initialization is in |SPARK|.


Discriminants
-------------

A ``discriminant_specification`` is in |SPARK| if its type is
discrete and it does not occur as part of a derived type declaration
whose parent type is discriminated. [In other words, inherited
discriminants shall not be hidden.]


Record Types
------------

|SPARK| does not permit partial default initialization of record objects.
More specifically, if at least one non-discriminant component (either
explicitly declared or inherited) of a record type or type extension either
is of a type which defines default initialization or is declared by
a component_declaration which includes a Default_Value, then the record type
or type extension shall define full default initialization.

[The enforcement of this rule requires looking at the ``full_type_declaration``
of a ``private_type`` declaration to determine whether the private type has a
default initialization. A future version of |SPARK| may introduce extra features
to avoid having to do this.]

Tagged Types and Type Extensions
--------------------------------

Use of the 'Class attribute is not permitted in |SPARK|.

[This restriction may be relaxed at some point in the future.
As a consequence of this restriction, dispatching calls are not currently in
|SPARK| but are planned for a future release.]

.. todo:: Add 'Class attribute to SPARK 2014. To be completed in a post-Release
          1 version of this document.

Type Extensions
~~~~~~~~~~~~~~~

A type extension declared within a subprogram body,
block statement, or generic body which does not also enclose the
declaration of each of its ancestor types is not in |SPARK|.


Dispatching Operations of Tagged Types
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Abstract Types and Subprograms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

No extensions or restrictions.


Interface Types
~~~~~~~~~~~~~~~

Use of ``interface_type_definition`` is not permitted in |SPARK|.

.. todo:: Include interface types in SPARK 2014. To be completed in a post-Release 1
          version of this document.


Access Types
------------

Access types allow the creation of aliased data structures and objects, which
notably complicate the specification and verification of a program's
behavior. Therefore, all forms of access type declaration are excluded from |SPARK|.

The attribute ``Access`` is not in |SPARK|.

Finally, as they are based on access discriminants, user-defined references
and user-defined indexing are not in |SPARK|.

Declarative Parts
-----------------

No extensions or restrictions.
