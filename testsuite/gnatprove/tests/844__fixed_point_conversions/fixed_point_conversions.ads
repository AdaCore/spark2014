package Fixed_Point_Conversions with SPARK_Mode is

   type Foo is delta 1.0 / 128.0 range -100.0 .. 100.0;

   type Bar is delta 1.0 / 8.0 range -20.0 .. 20.0;

   function Fixed_To_Fixed (X : Foo) return Bar is
     (Bar (X));

   function Fixed_To_Int (X : Foo) return Integer is
     (Integer (X))
   with Post => Foo (Fixed_To_Int'Result) = X;
   --  Roundings make the postcondition false for integers that are not
   --  divisible by 128

   function Int_To_Fixed (X : Integer) return Foo is
     (Foo (X));

end Fixed_Point_Conversions;
