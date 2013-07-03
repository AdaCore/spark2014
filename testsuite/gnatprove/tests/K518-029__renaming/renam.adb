package body Renam is
   procedure Set_X_Through_Y is
   begin
      Y := 1;
   end Set_X_Through_Y;

   procedure Set_X is
   begin
      Set_X_Through_Y;
   end Set_X;
end Renam;
