Exceptions
==========

Raising and handling of exceptions allow forms of control flow that complicate
both specification and verification of a program's behavior. This is the reason
explicit uses of exceptions are excluded from |SPARK|. For the same reasons 
``exception_handlers`` are prohibited in |SPARK|.

Exceptions can be raised implicitly (for example, by the failure of a
language-defined check), but only in the case of a program with an
undischarged (or incorrectly discharged, perhaps via an incorrect
Assume pragma) proof obligation.

The pragmas ``Assertion_Policy``, ``Suppress``, and ``Unsuppress`` are
allowed in |SPARK|, but have no effect on the generation of proof
obligations. For example, an array index value must be shown to be in
bounds regardless of whether Index_Check is suppressed at the point
of the array indexing.


