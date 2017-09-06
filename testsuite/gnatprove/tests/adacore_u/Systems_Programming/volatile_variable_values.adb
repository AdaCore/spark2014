package body Volatile_Variable_Values
  with SPARK_Mode
is
   procedure Check is
      N : Integer := Nat;
      A : Integer := Ang;
      S : Integer := Sub;
   begin
      pragma Assert (N >= 0);
      pragma Assert (A in 0 .. 360);
      pragma Assert (S in 0 .. 15 | 17 .. 42 | 43 .. 360);
   end Check;

   X : Integer with Volatile, Async_Readers;

   procedure Read_Value is
   begin
      X := 42;
      pragma Assert (X = 42);
   end Read_Value;

end Volatile_Variable_Values;
