procedure Decl1 with
   Global => null
is

   procedure Test (X : Integer) with
      Pre    => X = 0,
      Global => null
   is
      A : Integer := X with Alignment => 8;
      B : Integer := 1 with
         Address => A'Address, Alignment => 8;
   begin
      pragma Assert (A = 0); --@ASSERT:FAIL
   end;

begin
   Test (0);
end;
