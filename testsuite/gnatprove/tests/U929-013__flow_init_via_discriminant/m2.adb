procedure M2 (X : Natural) with Pre => (X < 1000)
is

   type T (D : Integer) is record
      C : Integer := D - 1;
   end record;

   subtype S is T (X + 1); --  ??? Overflow check should be prevented by precondition
   type P is access S;

   procedure Proc
     with Global => (Proof_In => X),
     --  Global contract is *correct* due to the following precondition
     Pre => P'(new S) /= null
     --  Memory leak may happen, for this test we don't care.
   is
   begin
       null;
   end;

begin
   null;
end M2;
