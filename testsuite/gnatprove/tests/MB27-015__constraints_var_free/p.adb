package body P
  with SPARK_Mode => On
is
   procedure Op (A : in out Integer)
   is
      -- A is "in out" so a variable not a constant, therefore...
      subtype LS4 is Integer range A .. 10;   -- illegal
   begin
      A := A + 2;
   end Op;
end P;
