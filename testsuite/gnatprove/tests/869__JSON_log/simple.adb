package body Simple with SPARK_Mode is

   function Foo (X, Y : T) return T is
   begin
      return X + Y;  --@COUNTEREXAMPLE
   end Foo;

   function Bar (X, Y : T) return T is
   begin
      return X * Y;  --@COUNTEREXAMPLE
   end Bar;

   function Sum_People (Alice, Bob : People) return Lifetime is
   begin
      return Alice.Age + Bob.Age;  --@COUNTEREXAMPLE
   end Sum_People;

   function Div_Float (N : Float) return Float is
   begin
      return 1.0 / (N - 3.1415);  --@COUNTEREXAMPLE
   end Div_Float;

   function Add_Array (A : My_Array) return T is
   begin
      return A (1) + A (2) + A (0);  --@COUNTEREXAMPLE
   end Add_Array;

   function Nested_CE (X, Y : T) return T is
      Z : T;
   begin
      Z := X + Y - 5;
      return Z / Z;  --@COUNTEREXAMPLE
   end Nested_CE;

   function Fixed_Point (X, Y : F) return F is
   begin
      return X * Y;  --@COUNTEREXAMPLE
   end Fixed_Point;

   function Obvious_Div_By_Zero (N : Integer) return Integer is
   begin
      return 1 / N;  --@COUNTEREXAMPLE
   end Obvious_Div_By_Zero;

   procedure Float_Precision (F : Float) is
   begin
      pragma Assert (F = 1.23456789);  --@COUNTEREXAMPLE
   end;

   procedure Check_Town (T : Town) is
      Total_Age : Integer := 0;
   begin
      for N in T.People'Range loop
         Total_Age := Total_Age + Integer (T.People (N).Age);
      end loop;
      pragma Assert (Total_Age > 420);  --@COUNTEREXAMPLE
   end Check_Town;

   procedure Mammals (A : Animal) is
   begin
      pragma Assert (A /= Chicken);  --@COUNTEREXAMPLE
   end Mammals;

   procedure Not_Michel (S : String) is
   begin
      pragma Assert (S /= "Michel");  --@COUNTEREXAMPLE
   end;

end Simple;
