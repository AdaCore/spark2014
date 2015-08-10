with Types; use Types;
with IMU_Pack; use IMU_Pack;
with Commander_Pack; use Commander_Pack;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions; use Interfaces.C.Extensions;

package Free_Fall_Pack
with SPARK_Mode,
  Abstract_State => (FF_State, FF_Parameters),
  Initializes    => (FF_State, FF_Parameters)
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
   --  Types

   --  Threshold used to detect when the drone is in Free Fall.
   --  This threshold is compared with accelerometer measurements for
   --  Z axis.
   subtype Free_Fall_Threshold is T_Acc range -0.2 .. 0.2;

   --  Type used to collect measurement samples and easily calculate
   --  their variance and mean.
   type FF_Acc_Data_Collector (Number_Of_Samples : Natural) is record
      Samples : T_Acc_Array (1 .. Number_Of_Samples) := (others => 0.0);
      Index   : Integer := 1;
   end record;

   --  Global variables and constants

   --  Number of samples we collect to calculate accelation variance
   --  along Z axis. Used to detect landing.
   LANDING_NUMBER_OF_SAMPLES : constant Natural := 15;

   --  Thrust related variables.
   MAX_RECOVERY_THRUST       : constant T_Uint16 := 59_000;
   MIN_RECOVERY_THRUST       : constant T_Uint16 := 30_000;
   RECOVERY_THRUST_DECREMENT : constant T_Uint16 := 100;

   --  Number of successive times that acceleration along Z axis must
   --  be in the threshold to detect a Free Fall.
   FF_DURATION :  T_Uint16 := 30
     with Part_Of => FF_Parameters;
   pragma Export (C, FF_DURATION, "ffDuration");

   --  If the variance is superior to this value during the recovering phase,
   --  it means that the drone has landed.
   LANDING_VARIANCE_THRESHOLD :  T_Alpha := 0.4
     with Part_Of => FF_Parameters;
   pragma Export (C, LANDING_VARIANCE_THRESHOLD, "landingVarianceThreshold");


   --  Used to enable or disable the Free Fall/Recovery feature.
   FF_Mode                            : Free_Fall_Mode := DISABLED
     with Part_Of => FF_Parameters;
   pragma Export (C, FF_Mode, "freeFallMode");

   --  Free Fall features internal variables.
   FF_Duration_Counter      : T_Uint16 := 0
     with Part_Of => FF_State;
   In_Recovery              : bool := 0
     with Part_Of => FF_State;
   Recovery_Thrust          : T_Uint16 := MAX_RECOVERY_THRUST
     with Part_Of => FF_State;
   Landing_Data_Collector   : FF_Acc_Data_Collector (LANDING_NUMBER_OF_SAMPLES)
     with Part_Of => FF_State;

   --  Procedures and functions

   --  Detect if the drone is in free fall with accelerometer data.
   procedure FF_Detect_Free_Fall
     (Acc         : Accelerometer_Data;
      FF_Detected : out Boolean);

   --  Detect if the drone has landed with accelerometer data.
   procedure FF_Detect_Landing (Landing_Detected : out Boolean);

   --  Add accelerometer sample for Z axis
   --  to the specified FF_Acc_Data_Collector.
   procedure Add_Acc_Z_Sample
     (Acc_Z          : T_Acc;
      Data_Collector : in out FF_Acc_Data_Collector);
   pragma Inline (Add_Acc_Z_Sample);

   --  Calculate variance and mean
   procedure Calculate_Variance_And_Mean
     (Data_Collector : FF_Acc_Data_Collector;
      Variance       : out Float;
      Mean           : out Float);
   pragma Inline (Calculate_Variance_And_Mean);

end Free_Fall_Pack;
