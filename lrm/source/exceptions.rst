Exceptions
==========

Raising and handling of exceptions allow forms of control flow that complicate
both specification and verification of a program's behavior. This is the reason
most explicit uses of exceptions are excluded from |SPARK| as described below.

Exceptions can be raised implicitly (for example, by the failure of a
language-defined check), but only in the case of a program with an
undischarged (or incorrectly discharged, perhaps via an incorrect
Assume pragma) proof obligation.

Explicit raising of exceptions is dealt with similarly.

A raise_statement introduces an obligation to prove that the statement
will not be executed, much like the proof obligation associated with

   pragma Assert (False);

In other words, the proof obligations introduced for a raise statement
are the same as those introduced for a runtime check which fails
unconditionally. A raise expression (see Ada AI12-0022 for details) introduces
a similar obligation to prove that the expression will not be evaluated.

Exception declarations (including exception renamings) are in [SPARK].
Raise statements and raise expressions are in [SPARK], but must
(as described above) be provably never executed.
Exception handlers are not in [SPARK].

The pragmas ``Assertion_Policy``, ``Suppress``, and ``Unsuppress`` are
allowed in |SPARK|, but have no effect on the generation of proof
obligations. For example, an array index value must be shown to be in
bounds regardless of whether Index_Check is suppressed at the point
of the array indexing.


