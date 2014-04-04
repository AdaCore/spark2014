package body Aggs
  with SPARK_Mode => On
is
   procedure Init1 (X : out A1)
   is
   begin
      X := A1'(1 => 6, others => <>); -- OK, since T1 has FDE
   end Init1;

   procedure Init2 (X : out A2)
   is
   begin
      X := A2'(1 => 16, others => <>); -- illegal
   end Init2;

   procedure Init3 (X : out A3)
   is
   begin
      X := A3'(others => <>); -- OK, since A3 has FDE
   end Init3;

   procedure Init4 (X : out AP1)
   is
   begin
      X := AP1'(1 => 6, others => <>); -- OK, since AP1 has FDE
   end Init4;

   procedure Init5 (X : out AP2)
   is
   begin
      X := AP2'(1 => 6, others => <>); -- illegal
   end Init5;
end Aggs;
