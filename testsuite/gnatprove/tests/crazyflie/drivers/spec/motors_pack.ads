with Types; use Types;

package Motors_Pack is

   --  Types

   type Motor_ID is (MOTOR_M1, MOTOR_M2, MOTOR_M3, MOTOR_M4);

   --  Procedures and functions

   procedure Motor_Set_Ratio
     (ID          : Motor_ID;
      Motor_Power : T_Uint16);

end Motors_Pack;
