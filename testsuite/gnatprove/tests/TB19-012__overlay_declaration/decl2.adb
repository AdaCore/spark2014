procedure Decl2 with
   Global => null
is


   type Int is new Integer with Default_Value => 1;

   procedure Test (X : Integer) with
      Pre    => X = 0,
      Global => null
   is
      A : Int := Int (X) with Alignment => 8;
      B : Int with
         Address => A'Address, Alignment => 8;
   begin
      pragma Assert (A = 0); --@ASSERT:FAIL
   end;

begin
   Test (0);
end;
