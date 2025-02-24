with Interfaces;
with Rover_HAL;
package Rover is

   function Cannot_Crash return Boolean
     with Pre => Rover_HAL.Initialized, Ghost;

private
   use type Interfaces.Unsigned_32;
   use type Rover_HAL.Motor_Power;

   function Cannot_Crash return Boolean is
     (Rover_HAL.Get_Power (Rover_HAL.Left)  <= 0 and then
      Rover_HAL.Get_Power (Rover_HAL.Right) <= 0);

end Rover;
