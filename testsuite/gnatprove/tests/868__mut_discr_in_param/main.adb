procedure Main is

   type R (D : Integer := 0) is record
      null;
   end record;

   procedure P
     (X : R)
      --  In parameters are always constrained. This precondition cannot be
      --  satisfied.
   with Pre => not X'Constrained;

   procedure P (X : R) is
   begin
      null;
   end P;

   U : R := (D => 1);

begin
   pragma Assert (not U'Constrained);
   P (U); -- @PRECONDITION:FAIL

end Main;
