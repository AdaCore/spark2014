Lexical Elements
================

|SPARK| supports the full Ada 2012 language with respect to lexical elements.
Users may choose to apply restrictions to simplify the use of wide character sets and strings.

Character Set
-------------

.. centered:: **Restrictions That May Be Applied**

.. include:: restrictions-and-profiles.rst
   :start-after: 2.1 Character Set
   :end-before:  6.1

Lexical Elements, Separators, and Delimiters
--------------------------------------------

No extensions or restrictions.

Identifiers
-----------

No extensions or restrictions.

Numeric Literals
----------------

No extensions or restrictions.

Character Literals
------------------

No extensions or restrictions.

String Literals
---------------

No extensions or restrictions.

Comments
--------

No extensions or restrictions.

Pragmas
-------

|SPARK| introduces a number of new pragmas that facilitate program verification.
These are introduced and documented below in the relevant sections of this document.

Reserved Words
--------------

|SPARK| has the same set of reserved words as Ada 2012.  Owing to language restrictions, the
following set of reserved words are never used in a |SPARK| program:

**abort**,
**accept**,
**access**,
**aliased**,
**delay**,
**entry**,
**exception**,
**goto**,
**protected**,
**raise**,
**requeue**,
**select**,
**synchronized**,
**task**,
**terminate**,
**until**.
