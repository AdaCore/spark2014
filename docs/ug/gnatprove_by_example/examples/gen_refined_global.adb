package body Gen_Refined_Global with
  SPARK_Mode,
  Refined_State => (State => V)
is
   V : Boolean;

   procedure Set_Global is
   begin
      V := True;
   end Set_Global;

   procedure Set_Global_Twice is
   begin
      Set_Global;
      Set_Global;
   end Set_Global_Twice;

   procedure Set_Global_Conditionally (X : Boolean) is
   begin
      if X then
         Set_Global;
      else
         Set_Global;
      end if;
   end Set_Global_Conditionally;

end Gen_Refined_Global;
