Declarations and Types
======================

|SPARK| does not add any declaration or type to Ada 2012, but it restricts
their usage.

Declarations
------------

The view of an entity is in |SPARK| if and only if the corresponding
declaration is in |SPARK|. When clear from the context, we say *entity* instead
of using the more formal term *view of an entity*.

Types and Subtypes
------------------

The view of an entity introduced by a ``private_type_declaration`` is in
|SPARK|, even if the entity declared by the corresponding
``full_type_declaration`` is not in |SPARK|.

.. todo::
  YM: The above must be refined. If the private type declaration has
  a visible discriminant, then the type of the discriminant should influence
  whether the private type is in |SPARK| or not. Target D1/CDR.

For a type or subtype to be in |SPARK|, all predicate specifications that apply
to the (sub)type must be in |SPARK|.  Notwithstanding any rule to the contrary,
a (sub)type is never in |SPARK| if its applicable predicate is not in |SPARK|.

Objects and Named Numbers
-------------------------

The entity declared by an object declaration is
in |SPARK| if its declaration does not contain the reserved word ``aliased``,
its type is in |SPARK|, and its initialization expression, if any, is in
|SPARK|.

.. todo:: TJJ and RCC think we need to allow for a deferred constant declaration
   to have a Global aspect here, to show the variables that the constant's
   value is derived from. Additionally, we need to allow for the deferred constant
   declaration to be in |SPARK| even if the completion is not in |SPARK|. Target: D1/CDR.

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

.. todo::
   RCC comment: What are our final intensions with respect to discriminated and variant
   record types? Trevor did a design of these for SPARK95 once, so this might
   prove some use as a starting point. I assume this won't be finalized for
   D1/CDR, so target for D2.

.. note::
  YM/3/1 no specific restrictions with discriminated and variant record types.
  They are already accepted in GNATprove.

Tagged Types and Type Extensions
--------------------------------

No extensions or restrictions.

.. todo::
   RCC comment: This will need to describe any global restrictions on tagged types (if any)
   and any additional Restrictions that we may feel users need.  I assume this section won't
   be finalized for D1/CDR, so target for D2.

.. todo::
   RCC comment: What are our intensions for Interface Types?  I must admit that no-one
   at Praxis understands these, so input from AdaCore very much welcome. As above, target for D2.

.. note::
  YM/3/2 no specific restrictions with interface types. Let us know what your
  questions are, we'll be happy to answer. Interfaces are tagged abstract types,
  and you can derive from more than one.

Access Types
------------

Access types allow the creation of aliased data structures and objects, which
notably complicate the specification and verification of a program's
behavior. Therefore, all forms of access type declaration are excluded from |SPARK|.

The attribute ``'Access`` is not in |SPARK|.

Finally, as they are based on access discriminants, user-defined references
and user-defined indexing are not in |SPARK|.

Declarative Parts
-----------------

No extensions or restrictions.
