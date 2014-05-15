procedure Context_B (X : Integer) with
  SPARK_Mode
is
   generic
      type Item is private;
      Compare_Against : Item;
      with function Cond (X : Item) return Boolean;
   package Gen
   is
      procedure Check_Cond;
   end Gen;

   package body Gen
   is
      procedure Check_Cond
      is
      begin
         pragma Assert (Cond (Compare_Against));
      end Check_Cond;
   end Gen;

   function Greater_Than_Zero (X : Integer) return Boolean is (X > 0);

   package Inst is new Gen (Integer, 6, Greater_Than_Zero);

   procedure Local is
   begin
      Inst.Check_Cond;
   end Local;
begin
   Local;
end Context_B;
