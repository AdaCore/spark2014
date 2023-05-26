procedure Raise_XXX_In_Decl with SPARK_Mode is

   function Id (I : Integer) return Integer is (I);
   type FIX is delta 0.5 range -3.0 .. 3.0;


   subtype SFX is FIX delta 0.1;
   SFX_VAR : SFX := FIX(Id(1));

begin
   null;
end Raise_XXX_In_Decl;
