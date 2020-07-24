package body Gen_Abstract_Global with
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

   procedure Set_Global_Conditionally (X : Boolean) with
     Refined_Global  => (Output => V),
     Refined_Depends => (V => X)
   is
   begin
      if X then
         Set_Global;
      else
         V := False;
      end if;
   end Set_Global_Conditionally;

end Gen_Abstract_Global;
