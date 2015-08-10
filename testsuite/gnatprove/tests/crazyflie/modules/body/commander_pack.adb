package body Commander_Pack is

   --  Procedures and functions
   procedure Commander_Get_RPY
     (Euler_Roll_Desired  : in out T_Degrees;
      Euler_Pitch_Desired : in out T_Degrees;
      Euler_Yaw_Desired   : in out T_Degrees) is
      procedure Commander_Get_RPY_Wrapper
        (Euler_Roll_Desired  : in out Float;
         Euler_Pitch_Desired : in out Float;
         Euler_Yaw_Desired   : in out Float);
      pragma Import (C, Commander_Get_RPY_Wrapper, "commanderGetRPY");
   begin
      Commander_Get_RPY_Wrapper
        (Euler_Roll_Desired,
         Euler_Pitch_Desired,
         Euler_Yaw_Desired);
      --  TODO: Smooth commands to have a better control
   end Commander_Get_RPY;

end Commander_Pack;
