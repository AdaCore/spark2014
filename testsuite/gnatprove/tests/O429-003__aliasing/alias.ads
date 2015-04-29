package Alias
  with SPARK_Mode
is
   G : Integer;
   procedure P (X : in out Integer)
     with Global => G;
   procedure Test;
end Alias;
