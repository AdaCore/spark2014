Declarations and Types
======================

|SPARK| does not add any declarations or types to Ada 2012, but it restricts
their usage.

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*.

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

The entity declared by an object declaration is
in |SPARK| if its declaration does not contain the reserved word **aliased**,
its type is in |SPARK|, and its initialization expression, if any, is in
|SPARK|.

Additionally, the view of an entity introduced by a deferred constant declaration is in
|SPARK|, even if the initializing expression in the corresponding completion is not in |SPARK|.

Derived Types and Classes
-------------------------

No extensions or restrictions.

Scalar Types
------------

No extensions or restrictions.

Array Types
-----------

No extensions or restrictions.

Discriminants
-------------

No extensions or restrictions.

Record Types
------------

No extensions or restrictions.

Tagged Types and Type Extensions
--------------------------------

No extensions or restrictions.

.. todo::
   RCC comment: This will need to describe any global restrictions on tagged types (if any)
   and any additional Restrictions that we may feel users need.  I assume this section won't
   be finalized for D1/CDR, so target for D2.

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
