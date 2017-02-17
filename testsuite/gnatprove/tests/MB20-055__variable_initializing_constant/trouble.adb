package body Trouble
  with SPARK_Mode => On
is
   procedure Op (X : in out Boolean)
   is
   begin
      X := not X;
   end Op;

begin
   V := 1;
end Trouble;
