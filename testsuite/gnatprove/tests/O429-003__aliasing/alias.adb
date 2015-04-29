package body Alias
  with SPARK_Mode
is
   procedure P (X : in out Integer) is
   begin
      X := G + X;
   end P;
   procedure Test is
   begin
      P (G);
   end Test;
end Alias;
