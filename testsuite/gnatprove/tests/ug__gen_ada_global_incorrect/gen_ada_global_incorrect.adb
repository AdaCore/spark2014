package body Gen_Ada_Global_Incorrect with
  SPARK_Mode
is
   G : Holder;

   procedure Set_Access_To_Variable (V : in Holder) with SPARK_Mode => Off
   is
   begin
      V.I.all := 0;
   end Set_Access_To_Variable;

   procedure Set_Global_Access with SPARK_Mode => Off
   is
   begin
      Set_Access_To_Variable (G);
   end Set_Global_Access;

   procedure Test is
   begin
      Set_Global_Access;
   end Test;

end Gen_Ada_Global_Incorrect;
