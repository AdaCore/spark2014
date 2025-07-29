package body Gen_Ada_Global_Access_To_Procedure with
  SPARK_Mode
is
   V : Boolean;

   procedure Set_Global with
     SPARK_Mode => Off
   is
      procedure Set_V
      is
      begin
         V := True;
      end Set_V;

      type P_Access is access procedure;

      Set_V_Acc : P_Access := Set_V'Access;
   begin
      Set_V_Acc.all;
   end Set_Global;

   procedure Set_Global_Through_Access_To_Procedure is
   begin
      Set_Global;
   end Set_Global_Through_Access_To_Procedure;

end Gen_Ada_Global_Access_To_Procedure;
