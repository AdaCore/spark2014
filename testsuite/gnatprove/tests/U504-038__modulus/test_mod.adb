procedure Test_Mod with SPARK_Mode is
   type U is mod 2**9;
   type S is mod 2**8;
   type T is mod 2**7;
   function Id (X : S) return S is (X);
   function Id2 (X : U) return U is (X);
begin
   pragma Assert (T'Modulus = Id (2**7));
   pragma Assert (T'Mod (Id (2**7)) = 0);
   pragma Assert (S'Mod (Id2 (2**7)) = 2**7);
end Test_Mod;
