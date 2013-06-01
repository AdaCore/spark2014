Declarations and Types
======================

Declarations
------------

The view of an entity is in Alfa if and only if the corresponding declaration
is in Alfa. When clear from the context, we say *entity* instead of using the
more formal term *view of an entity*.

Types and Subtypes
------------------

The view of an entity introduced by a ``private_type_declaration`` is in Alfa,
even if the entity declared by the corresponding
``full_type_declaration`` is not in Alfa.

For a type or subtype to be in Alfa, all predicate specifications that apply to
the (sub)type must be in Alfa.  Notwithstanding any rule to the contrary, a
(sub)type is never in Alfa if its applicable predicate is not in Alfa.

Objects and Named Numbers
-------------------------

No specific restrictions. Thus, the entity declared by an object declaration is
in Alfa if its declaration does not contain the reserved word ``aliased``, its
type is in Alfa, and its initialization expression, if any, is in Alfa.

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

Tagged Types and Type Extensions
--------------------------------

No specific restrictions.

Access Types
------------

Access types allow the creation of aliased data structures and objects, which
notably complicate the specification and verification of a program's
behavior. This is the reason access types are excluded from Alfa. This
falls out without any specific restrictions from the reserved word ``access``
not being in Alfa.

Additionally, values of type access-to-subprogram make it impossible to compute
the global parameters of subprograms and to detect aliasing. This excludes all
forms of access-to-subprogram types in Alfa friendly code.

Declarative Parts
-----------------

No specific restrictions.
