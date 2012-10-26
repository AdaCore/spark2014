Declarations and Types
======================

There are no added features in this section, only restrictions.

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

For a type or subtype to be in |SPARK|, all predicate specifications that apply
to the (sub)type must be in |SPARK|.  Notwithstanding any rule to the contrary,
a (sub)type is never in |SPARK| if its applicable predicate is not in |SPARK|.

Objects and Named Numbers
-------------------------

No specific restrictions. Thus, the entity declared by an object declaration is
in |SPARK| if its declaration does not contain the reserved word ``aliased``,
its type is in |SPARK|, and its initialization expression, if any, is in
|SPARK|.

Derived Types and Classes
-------------------------

No specific restrictions.

Scalar Types
------------

No specific restrictions.

Array Types
-----------

No specific restrictions.

Discriminants
-------------

No specific restrictions.

Record Types
------------

No specific restrictions.

.. todo::
   RCC comment: What are our final intensions with respect to discriminated and variant
   record types? Trevor did a design of these for SPARK95 once, so this might
   prove some use as a starting point. I assume this won't be finalized for
   D1/CDR, so target for D2.

 
Tagged Types and Type Extensions
--------------------------------

No specific restrictions.

.. todo::
   RCC comment: This will need to describe any global restrictions on tagged types (if any)
   and any additional Restrictions that we may feel users need.  I assume this section won't
   be finalized for D1/CDR, so target for D2.

.. todo::
   RCC comment: What are our intensions for Interface Types?  I must admit that no-one
   at Praxis understands these, so input from AdaCore very much welcome. As above, target for D2.


Access Types
------------

Access types allow the creation of aliased data structures and objects, which
notably complicate the specification and verification of a program's
behavior. This is the reason access types are excluded from |SPARK|. This falls
out without any specific restrictions from the reserved word ``access`` not
being allowed in |SPARK|.

.. note::
   RCC/3/1 Simply saying that the reserved word is not allowed is a bit low-tech!
   This seems to imply some sort of lexical/syntactic restriction, which is, of 
   course, not the way it's implemented.  Would it be better to say that all
   forms of access type declaration are forbidden?

Declarative Parts
-----------------

No specific restrictions.
