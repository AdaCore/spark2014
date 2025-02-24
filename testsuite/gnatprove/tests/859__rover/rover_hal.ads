with Interfaces; use Interfaces;

package Rover_HAL
with
  Abstract_State => (HW_Init, (HW_State with Synchronous)),
  Initializes    => (HW_State),
  SPARK_Mode,
  Always_Terminates
is

   function Initialized return Boolean
     with Global => HW_Init;

   procedure Initialize
     with
       Global => (Output => HW_Init),
       Post   => Initialized;

   type Side_Id is (Left, Right) with Size => 8;

   type Motor_Power is new Interfaces.Integer_8 range -100 .. 100;

   procedure Set_Power (Side : Side_Id;
                        Pwr  : Motor_Power)
     with
       Pre  => Initialized,
       Post => Initialized and then
               Get_Power (Side) = Pwr,
       Global => (HW_State, HW_Init);

   function Get_Power (Side : Side_Id) return Motor_Power
     with
       Pre => Initialized,
       Global => HW_Init,
       Ghost,
       Import;
   --  Return the value set in the last call to `Set_Power`.

end Rover_HAL;
