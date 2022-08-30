procedure Nonbinary is

   type T is mod 14;

   function One return T is (1);

   X : T := One;
begin
   X := not X;
   pragma Assert (X = 2);
   pragma Assert (X = 3); --@ASSERT:FAIL
end Nonbinary;
