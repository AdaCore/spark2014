Declarations and Types
======================

|SPARK| does not add any declarations or types to Ada 2012, but it restricts
their usage.

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*.

Certain type and subtype declarations can specify a default value to be given to 
declared objects of the (sub)type.  There are several syntatic names and schemes
for defining the default value: the ``default_expression`` of discriminants and 
record components, Default_Value aspect of scalar types and 
Default_Component_Value aspect for an array-of-scalar subtype.  
These are collectively known as *default initialization*.

Types and Subtypes
------------------

The view of an entity introduced by a ``private_type_declaration`` is in
|SPARK| if the types of any visible discriminants are in |SPARK|, even if the entity
declared by the corresponding ``full_type_declaration`` is not in |SPARK|.

For a type or subtype to be in |SPARK|, all predicate specifications that apply
to the (sub)type must be in |SPARK|.  Notwithstanding any rule to the contrary,
a (sub)type is never in |SPARK| if its applicable predicate is not in |SPARK|.

Objects and Named Numbers
-------------------------

The entity declared by an ``object_declaration`` is
in |SPARK| if its declaration does not contain the reserved word **aliased**,
its type is in |SPARK|, and its *initialization_*\ ``expression``, if any, is in
|SPARK|.

Additionally, the view of an entity introduced by a
``deferred_constant_declaration`` is in |SPARK|, even if the *initialization_*\
``expression`` in the corresponding completion is not in |SPARK|.


Derived Types and Classes
-------------------------

An entity declared by a ``derived_type`` declaration is in |SPARK| if its 
parent type is in |SPARK|, and if the declaration contains an ``interface_list`` 
or a ``record_part`` these must also contain entities that are in |SPARK|.

Scalar Types
------------

A scalar type declaration is in |SPARK| unless it has a default initialization
that is not in |SPARK|.

Array Types
-----------

An entity declared by a ``array_type_definition`` is in |SPARK| if its 
components are in |SPARK| and default initialization is in |SPARK|.


Discriminants
-------------

A ``discriminant_part`` is in |SPARK| if it is not an access type and its
default initialization, if any, is in |SPARK|

Record Types
------------

An entity declared by a ``record_type_definition`` is in |SPARK| if all of its 
components are in |SPARK| and if a component has a default initialization then
all of the components must have a default initialization.  
A default initialization, if present must also be in |SPARK|.

|SPARK| does not permit partial default initialization of record objects.

Tagged Types and Type Extensions
--------------------------------

No extensions or restrictions currently identified, though see ToDo.

.. todo::
   RCC comment: This will need to describe any global restrictions on tagged types (if any)
   and any additional Restrictions that we may feel users need.
   To be completed in the Milestone 4 version of this document.

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
