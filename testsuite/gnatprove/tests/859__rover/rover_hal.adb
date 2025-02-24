package body Rover_HAL
with SPARK_Mode => Off
is

   HW_Initialized : Boolean := False;

   function Initialized return Boolean is
   begin
      return HW_Initialized;
   end Initialized;

   procedure Initialize is
   begin
      HW_Initialized := True;
   end Initialize;

   procedure Set_Power (Side : Side_Id;
                        Pwr  : Motor_Power) is
   begin
     null;
   end Set_Power;

end Rover_HAL;
