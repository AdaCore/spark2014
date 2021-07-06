procedure Test_Or_Mod with SPARK_Mode is
   type S is mod 5;
   function Id (X : S) return S is (X);
   X : S := 3;
   Y : S := 4;
begin
   pragma Assert ((Id (X) or Id (Y)) = 2);
   pragma Assert ((Id (X) xor Id (Y)) = 2);
end Test_Or_Mod;
