with Ada.Real_Time; use Ada.Real_Time;

with Types; use Types;
with IMU_Pack; use IMU_Pack;
with Commander_Pack; use Commander_Pack;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions; use Interfaces.C.Extensions;

package Free_Fall_Pack
with SPARK_Mode,
  Abstract_State => (FF_State),
  Initializes    => (FF_State)
is
   --  Types

   type Free_Fall_Mode is (DISABLED, ENABLED);
   for Free_Fall_Mode use (DISABLED => 0, ENABLED => 1);
   for Free_Fall_Mode'Size use Interfaces.C.int'Size;

   --  Procedures and functions

   --  Check if an event (Free fall or Landing) has occured giving it
   --  accelerometer data.
   procedure FF_Check_Event (Acc : Accelerometer_Data);

   --  Override the previous commands if in recovery mode.
   procedure FF_Get_Recovery_Commands
     (Euler_Roll_Desired  : in out Float;
      Euler_Pitch_Desired : in out Float;
      Roll_Type           : in out RPY_Type;
      Pitch_Type          : in out RPY_Type);

   --  Override the previous thrust if in recovery mode.
   procedure FF_Get_Recovery_Thrust (Thrust : in out T_Uint16);

private
   --  Constants

   --  Number of samples we collect to calculate accelation variance
   --  along Z axis. Used to detect landing.
   LANDING_NUMBER_OF_SAMPLES : constant Natural := 15;

   --  Thrust related variables.
   MAX_RECOVERY_THRUST       : constant T_Uint16 := 48_000;
   MIN_RECOVERY_THRUST       : constant T_Uint16 := 22_000;
   RECOVERY_THRUST_DECREMENT : constant T_Uint16 := 100;

   --  Number of successive times that acceleration along Z axis must
   --  be in the threshold to detect a Free Fall.
   FF_DURATION               : constant T_Uint16 := 30;

   --  Stabiliation period after a landing, during which free falls can't
   --  be detected.
   STABILIZATION_PERIOD_AFTER_LANDING : constant Time_Span
     := Milliseconds (1_000);
   --  Used by a watchdog to ensure that we cut the thrust after a free fall,
   --  even if the drone has not recovered.
   RECOVERY_TIMEOUT                   : constant Time_Span
     := Milliseconds (6_000);

   --  If the derivative is superior to this value during the recovering phase,
   --  it means that the drone has landed.
   LANDING_DERIVATIVE_THRESHOLD       : constant T_Alpha := 0.25;

   --  Types

   --  Threshold used to detect when the drone is in Free Fall.
   --  This threshold is compared with accelerometer measurements for
   --  Z axis.
   subtype Free_Fall_Threshold is T_Acc range -0.2 .. 0.2;

   --  Type used to prove that we can't have a buffer overflow
   --  when collecting accelerometer samples.
   subtype T_Acc_Data_Collector_Index is
     Integer range 1 .. LANDING_NUMBER_OF_SAMPLES;

   --  Type used to collect measurement samples and easily calculate
   --  their variance and mean.
   type FF_Acc_Data_Collector  is record
      Samples : T_Acc_Array (T_Acc_Data_Collector_Index) := (others => 0.0);
      Index   : T_Acc_Data_Collector_Index := 1;
   end record;

   --  Global variables

   --  Used to enable or disable the Free Fall/Recovery feature.
   FF_Mode                            : Free_Fall_Mode := ENABLED
     with Part_Of => FF_State;

   --  Free Fall features internal variables.
   FF_Duration_Counter      : T_Uint16 := 0
     with Part_Of => FF_State;
   In_Recovery              : bool := False
     with Part_Of => FF_State;
   Recovery_Thrust          : T_Uint16 := MAX_RECOVERY_THRUST
     with Part_Of => FF_State;
   Last_Landing_Time        : Time := Time_First
     with Part_Of => FF_State;
   Last_FF_Detected_Time    : Time := Time_First
     with Part_Of => FF_State;
   Landing_Data_Collector   : FF_Acc_Data_Collector
     with Part_Of => FF_State;

   --  Procedures and functions

   --  Detect if the drone is in free fall with accelerometer data.
   procedure FF_Detect_Free_Fall
     (Acc         : Accelerometer_Data;
      FF_Detected : out Boolean);

   --  Detect if the drone has landed with accelerometer data.
   procedure FF_Detect_Landing (Landing_Detected : out Boolean);

   --  Ensures that we cut the recovery after a certain time, even if it has
   --  not recovered.
   procedure FF_Watchdog;

   --  Add accelerometer sample for Z axis
   --  to the specified FF_Acc_Data_Collector.
   procedure Add_Acc_Z_Sample
     (Acc_Z          : T_Acc;
      Data_Collector : in out FF_Acc_Data_Collector);
   pragma Inline (Add_Acc_Z_Sample);

   --  Calculate the derivative from the two last samples collected.
   function Calculate_Last_Derivative
     (Data_Collector : FF_Acc_Data_Collector) return Float;

   --  Get the time since last landing after a recovery from a free fall.
   function Get_Time_Since_Last_Landing return Time_Span
   with Volatile_Function;
   pragma Inline (Get_Time_Since_Last_Landing);

   --  Get the time since the last free fall detection.
   function Get_Time_Since_Last_Free_Fall return Time_Span
   with Volatile_Function;

end Free_Fall_Pack;
