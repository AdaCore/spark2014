Packages
========

A package is not by itself in Alfa or not. What matters is that it contains the
declarations of entities which are in Alfa or not. 

Private Types and Private Extensions
------------------------------------

The partial view of a private type may in Alfa even if its full view is not in
Alfa.

Type Invariants
---------------

The Ada 2012 RM lists places at which an invariant check is performed. In Alfa,
we add the following places:

  * Before a call on any subprogram or entry that: 

    * is explicitly declared within the immediate scope of type T (or by an
      instance of a generic unit, and the generic is declared within the
      immediate scope of type T), and

    * is visible outside the immediate scope of type T or overrides an
      operation that is visible outside the immediate scope of T, and

    * has one or more in out or in parameters with a part of type T.

    the check is performed on each such part of type T. 

Assignment and Finalization
---------------------------

Controlled types are not Alfa friendly.
