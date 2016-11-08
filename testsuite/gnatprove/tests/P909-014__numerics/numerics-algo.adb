package body Numerics.Algo
with SPARK_Mode
is

   procedure Algo (X  : in T_Float;
                   X1 : out T_Float;
                   X2 : out T_Float;
                   X3 : out T_Float;
                   X4 : out T_Float;
                   X5 : out T_Float) is
   begin
      X1 := T_Float'Last;
      X1 := X1 + X1;
      X2 := T_Float'Last;
      X2 := -X2 - X2;
      X3 := T_Float'Last;
      X3 := X3 * X3;
      X4 := 3.0;
      X4 := 1.0 / (X4 - X4);
      X5 := 1.0 / X;
   end Algo;

end Numerics.Algo;
