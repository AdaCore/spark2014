procedure Main (X : Positive) with SPARK_Mode is

   type T (D : Positive) is record
      C : Integer := D - 1;
   end record;

   type T_Arr is array (Positive range <>) of T (X);

begin
   pragma Assert (T'(D => X, others => <>).C = X - 1);
   pragma Assert (T_Arr'(1 .. 5 => <>) (1).C = X - 1);
end;
