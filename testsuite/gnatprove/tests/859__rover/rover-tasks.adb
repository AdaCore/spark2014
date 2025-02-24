package body Rover.Tasks
with SPARK_Mode
is

   ----------
   -- Demo --
   ----------

   procedure Demo is
   begin
      Rover_HAL.Set_Power (Rover_HAL.Left, 100);
   end Demo;

end Rover.Tasks;
