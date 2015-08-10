package body Motors_Pack is

   procedure Motor_Set_Ratio
     (ID          : Motor_ID;
      Motor_Power : T_Uint16) is

      procedure Motor_Set_Ratio_Wrapper
        (ID          : T_Int16;
         Motor_Power : T_Uint16);
      pragma Import (C, Motor_Set_Ratio_Wrapper, "motorsSetRatio");
   begin
      Motor_Set_Ratio_Wrapper (Motor_ID'Pos (ID), Motor_Power);
   end Motor_Set_Ratio;

end Motors_Pack;
