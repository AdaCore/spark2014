General
=======

Alfa is a subset of Ada 2012 suitable for automatic formal verification of
programs. Alfa builds on the capability to specify contracts for subprograms in
Ada 2012, which supports modular verification of subprograms by unit testing or
unit proving: a subprogram with a contract can be unit tested; a subprogram in
Alfa with a contract can also be unit proved. In order to combine the results
of unit testing and unit proving, the complete program should be *Alfa
friendly*, so that the assumptions made during unit proving of a subprogram can
be dynamically verified during unit testing of a caller or callee of this
subprogram.

Alfa restricts language features to remove the possibilities of non-determinism
and to make automatic proof possible. For example, it excludes access types,
exceptions and controlled types, and it restricts functions (but not
procedures) to be pure. In the rest of this document, we say that a construct
is pure, or equivalently free from side-effects, if its evaluation cannot
modify the value of a variable or memory location. Some restrictions are
syntactic, like ``explicit_dereference`` is not in Alfa, others are semantic,
like ``implicit_dereference`` is not in Alfa. If not stated otherwise, a
construct is in Alfa.

The Alfa friendly profile restricts language features so that the global
parameters of subprograms are computable, and that aliasing can be
detected. for example, it excludes calls through access to subprograms and
controlled types. It is equivalent to the following set of restrictions:

.. code-block:: ada

   pragma Restrictions (
            No_Access_Subprograms,
            No_Finalization,
            No_Implicit_Aliasing,
	    No_Parameter_Aliasing,
            No_Uninitialized_Parameters);

This document defines both the the Alfa restriction and the Alfa friendly
profile.

