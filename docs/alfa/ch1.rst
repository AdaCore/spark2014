General
=======

Alfa is a subset of Ada 2012 suitable for automatic formal verification of
programs. Alfa builds on the capability of specifying contracts for subprograms
provided in Ada 2012. Alfa supports modular verification of subprograms by unit
testing or unit proving: a subprogram with a contract can be unit tested; a
subprogram in Alfa with a contract can also be unit proved.  In order to
combine the results of unit testing and unit proving, the complete program
should be *Alfa friendly*, so that the assumptions made during unit proving of
a subprogram can be dynamically verified during unit testing of a caller or
callee of this subprogram.

Alfa restricts language features to remove the possibility of nondeterminism
and to make automatic proof possible. For example, it excludes access types,
exceptions, and controlled types, and it requires functions (but not
procedures) to be pure. Some restrictions are syntactic (e.g.,
``explicit_dereference`` is not in Alfa) and other restrictions are semantic
(e.g., ``implicit_dereference`` is not in Alfa). Unless stated otherwise, a
construct is in Alfa.

The Alfa-friendly profile restricts language features so that the global
parameters of subprograms are computable, and aliasing can be detected. For
example, it excludes controlled types and calls through access-to-subprogram
values.  It is equivalent to the following set of restrictions:

.. code-block:: ada

   pragma Restrictions (
            No_Access_Subprograms,
            No_Finalization,
            No_Implicit_Aliasing,
	    No_Parameter_Aliasing,
            No_Uninitialized_Parameters);

Note that some restrictions can be detected statically, while others (aliasing,
initialization) must be detected at run-time. This document defines both the
Alfa subset of Ada 2012 and the Alfa-friendly profile.

Purity
------

In the rest of this document, we say that a construct is pure, or,
equivalently, free from side effects, if its evaluation cannot modify the value
of a variable or memory location. Note that this is not the same as the Ada
term "pure", which applies to packages whose declarations satisfy certain
criteria that are somewhat related to but not the same as the Alfa notion of
purity.

Dynamic Semantics
-----------------

The Alfa-friendly profile augments the dynamic semantics of Ada with additional
run-time checks. At the cost of this additional verification, we get a valid
combination between unit testing and unit proving of subprograms in an
Alfa-friendly program. To get this benefit, tools for unit testing/proving must
take into account the additional run-time checks. For example, this can be a
special mode of the compiler for unit testing.
