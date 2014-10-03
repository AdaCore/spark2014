package body Aggs
  with SPARK_Mode => On
is
   procedure Init1 (X : out A1)
   is
   begin
      X := A1'(1 => 6, others => <>);
   end Init1;

   procedure Init2 (X : out A2)
   is
   begin
      X := A2'(others => <>);
   end Init2;

   procedure Init3 (X : out AP1)
   is
   begin
      X := AP1'(1 => 6, others => <>);
   end Init3;

   procedure Init4 (X : out A2)
   is
   begin
      X := A2'(others => 11);
   end Init4;

end Aggs;
