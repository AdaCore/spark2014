Refinement of contracts
=======================

In Ada 2012, ``Pre`` and ``Post`` aspects can be declared for a subprogram
declaration only. Here we allow that in addition, a refined contract can be
given on the body of a subprogram.

Dynamic semantics
-----------------

If it exists, the contract of the body is checked at runtime.

Proof semantics
---------------

If the contract of the body is visible, this contract can be used for proof.
Otherwise, the contract on the declaration is used. If two contracts are
given, it must be proved that the precondition on the declaration implies the
precondition of the body, and that the postcondition of the body implies the
postcondition of the declaration.

Example
-------

::

   function F (X : T; Y : Integer) return Integer
   with Pre  => Y > 10,
        Post => F'Result > Y;

   function F (X : T; Y : Integer) return Integer
   with Pre  => Y > 10,
        Post => F'Result = Y + X.A;
   is
   begin
      ...
   end F;

In this example, it is clear that the more precise postcondition of the body
implies the postcondition of the declaration. Callers who have visibility of
the body can use this more precise postcondition; others need to use the
coarser one.
