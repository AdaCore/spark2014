with Ada.Real_Time;
with Interfaces.C.Extensions; use Interfaces.C.Extensions;

with Types; use Types;
with IMU_Pack; use IMU_Pack;
with LPS25h_pack; use LPS25h_pack;
with Pid_Pack;
pragma Elaborate_All (Pid_Pack);
with Pid_Parameters; use Pid_Parameters;
with Commander_Pack; use Commander_Pack;
with Controller_Pack; use Controller_Pack;
with Free_Fall_Pack; use Free_Fall_Pack;
with SensFusion6_Pack; use SensFusion6_Pack;

package Stabilizer_Pack
with SPARK_Mode,
  Abstract_State => (IMU_Outputs,
                     Actual_Angles,
                     Desired_Angles,
                     Desired_Rates,
                     Command_Types,
                     Actuator_Commands,
                     Motor_Powers,
                     V_Speed_Parameters,
                     Asl_Parameters,
                     Alt_Hold_Parameters,
                     V_Speed_Variables,
                     Asl_Variables,
                     Alt_Hold_Variables),
  Initializes    => (IMU_Outputs,
                     Actual_Angles,
                     Desired_Angles,
                     Desired_Rates,
                     Command_Types,
                     Actuator_Commands,
                     Motor_Powers,
                     V_Speed_Parameters,
                     Asl_Parameters,
                     Alt_Hold_Parameters,
                     V_Speed_Variables,
                     Asl_Variables,
                     Alt_Hold_Variables)
is
   --  Instantiation of PID generic package for Altitude
   package Altitude_Pid is new Pid_Pack
     (T_Altitude'First,
      T_Altitude'Last,
      Float'First / 8.0,
      Float'Last / 8.0,
      MIN_ALTITUDE_COEFF,
      MAX_ALTITUDE_COEFF);

   --  Procedures and functions

   --  C function for Alt Hold Mode (Test)
   procedure C_Stabilizer_Alt_Hold_Update;
   pragma Import (C, C_Stabilizer_Alt_Hold_Update, "stabilizerAltHoldUpdate");

   --  Main function of the stabilization system. Get the commands, give them
   --  to the PIDs, and get the output to control the actuators.
   procedure Stabilizer_Control_Loop
     (Attitude_Update_Counter : in out T_Uint32;
      Alt_Hold_Update_Counter : in out T_Uint32)
     with
       Global => (Input  => (V_Speed_Parameters,
                             Asl_Parameters,
                             Alt_Hold_Parameters,
                             Ada.Real_Time.Clock_Time),
                  In_Out => (FF_State,
                             SensFusion6_State,
                             IMU_Outputs,
                             Desired_Angles,
                             Desired_Rates,
                             Actual_Angles,
                             Command_Types,
                             Actuator_Commands,
                             Motor_Powers,
                             Attitude_PIDs,
                             Rate_PIDs,
                             V_Speed_Variables,
                             Asl_Variables,
                             Alt_Hold_Variables));
   pragma Export (C, Stabilizer_Control_Loop, "ada_stabilizerControlLoop");

   --  Function called when Alt_Hold mode is activated. Holds the drone
   --  at a target altitude.
   procedure Stabilizer_Alt_Hold_Update
     with
       Global => (Input   => (Asl_Parameters,
                              Alt_Hold_Parameters,
                              V_Speed_Parameters),
                  In_Out  => (V_Speed_Variables,
                              Asl_Variables,
                              Alt_Hold_Variables,
                              Actuator_Commands));

   --  Update the Attitude PIDs.
   procedure Stabilizer_Update_Attitude
     with
       Global => (Input  => (Desired_Angles,
                             IMU_Outputs,
                             V_Speed_Parameters),
                  Output => (Actual_Angles,
                             Desired_Rates),
                  In_Out => (SensFusion6_State,
                             V_Speed_Variables,
                             Attitude_PIDs));

   --  Update the Rate PIDs.
   procedure Stabilizer_Update_Rate
     with
       Global => (Input  => (Command_Types,
                             Desired_Angles,
                             IMU_Outputs),
                  In_Out => (Actuator_Commands,
                             Desired_Rates,
                             Rate_PIDs));

private

   --  Global variables and constants

   --  Defines in what divided update rate should the attitude
   --  control loop run relative the rate control loop.

   ATTITUDE_UPDATE_RATE_DIVIDER   : constant := 2;
   ATTITUDE_UPDATE_RATE_DIVIDER_F : constant := 2.0;
   --  500 Hz
   FUSION_UPDATE_DT : constant Float :=
                        (1.0 / (IMU_UPDATE_FREQ
                         / ATTITUDE_UPDATE_RATE_DIVIDER_F));

   --  500hz/5 = 100hz for barometer measurements
   ALTHOLD_UPDATE_RATE_DIVIDER   : constant := 5;
   ALTHOLD_UPDATE_RATE_DIVIDER_F : constant := 5.0;
   --  200 Hz
   ALTHOLD_UPDATE_DT : constant Float :=
                                     (1.0 / (IMU_UPDATE_FREQ
                                      / ALTHOLD_UPDATE_RATE_DIVIDER_F));

   --  IMU outputs. The IMU is composed of an accelerometer, a gyroscope
   --  and a magnetometer (notused yet)
   Gyro : Gyroscope_Data     := (0.0, 0.0, 0.0)
     with Part_Of => IMU_Outputs;
   Acc  : Accelerometer_Data := (0.0, 0.0, 0.0)
     with Part_Of => IMU_Outputs;
   Mag  : Magnetometer_Data  := (0.0, 0.0, 0.0)
     with Part_Of => IMU_Outputs;

   --  Actual angles. These angles are calculated by fusing
   --  accelerometer and gyro data in the Sensfusion algorithms.
   Euler_Roll_Actual   : T_Degrees := 0.0
     with Part_Of => Actual_Angles;
   Euler_Pitch_Actual  : T_Degrees := 0.0
     with Part_Of => Actual_Angles;
   Euler_Yaw_Actual    : T_Degrees := 0.0
     with Part_Of => Actual_Angles;

   --  Desired angles. Obtained directly from the pilot.
   Euler_Roll_Desired  : T_Degrees := 0.0
     with Part_Of => Desired_Angles;
   Euler_Pitch_Desired : T_Degrees := 0.0
     with Part_Of => Desired_Angles;
   Euler_Yaw_Desired   : T_Degrees := 0.0
     with Part_Of => Desired_Angles;

   --  Desired rates. Obtained directly from the pilot when
   --  commands are in RATE mode, or from the rate PIDs when commands
   --  are in ANGLE mode
   Roll_Rate_Desired   : T_Rate  := 0.0
     with Part_Of => Desired_Rates;
   Pitch_Rate_Desired  : T_Rate  := 0.0
     with Part_Of => Desired_Rates;
   Yaw_Rate_Desired    : T_Rate  := 0.0
     with Part_Of => Desired_Rates;

   --  Variables used to calculate the altitude above see level (ASL)
   Temperature  : T_Temperature := 0.0 --  Temperature
     with Part_Of => Asl_Variables;
   Pressure     : T_Pressure    := 1000.0
     with Part_Of => Asl_Variables;    --  Pressure from barometer
   Asl          : T_Altitude    := 0.0
     with Part_Of => Asl_Variables;    --  Smoothed asl
   Asl_Raw      : T_Altitude    := 0.0
     with Part_Of => Asl_Variables;    --  Raw asl
   Asl_Long     : T_Altitude    := 0.0
     with Part_Of => Asl_Variables;    --  Long term asl

   --  Variables used to calculate the vertical speed
   Acc_WZ       : Float   := 0.0
     with Part_Of => V_Speed_Variables;
   Acc_MAG      : Float   := 0.0
     with Part_Of => V_Speed_Variables;
   V_Speed_ASL  : T_Speed := 0.0
     with Part_Of => V_Speed_Variables;
   V_Speed_Acc  : T_Speed   := 0.0
     with Part_Of => V_Speed_Variables;
   V_Speed      : T_Speed := 0.0
     with Part_Of => V_Speed_Variables; --  Vertical speed (world frame)
                                        --  integrated from vertical
                                        --  acceleration

   --  Variables used for the Altitude Hold mode
   Alt_Hold_PID : Altitude_Pid.Pid_Object :=
                    (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0,
                     0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.1)
     with Part_Of => Alt_Hold_Variables; --  Used for altitute hold mode.
                                         --  It gets reset when the bat status
                                         --  changes
   Alt_Hold     : bool := False
     with Part_Of => Alt_Hold_Variables; --  Currently in altitude hold mode
   Set_Alt_Hold : bool := False
     with Part_Of => Alt_Hold_Variables; --  Hover mode has just been activated
   Alt_Hold_PID_Val : T_Altitude := 0.0
     with Part_Of => Alt_Hold_Variables; --  Output of the PID controller
   Alt_Hold_Err     : Float := 0.0
     with Part_Of => Alt_Hold_Variables; --  Altitude error
   Alt_Hold_Change      : T_Altitude := 0.0
     with Part_Of => Alt_Hold_Variables; --  Change in target altitude
   Alt_Hold_Target      : T_Altitude := -1.0
     with Part_Of => Alt_Hold_Variables; --  Target altitude

   --  Altitude hold & barometer params

   --  PID gain constants used everytime we reinitialise the PID controller
   ALT_HOLD_KP          : constant Float := 0.5;
   ALT_HOLD_KI          : constant Float := 0.18;
   ALT_HOLD_KD          : constant Float := 0.0;

   --  Parameters used to calculate the vertical speed
   V_Speed_ASL_Fac      : T_Speed := 0.0
     with Part_Of => V_Speed_Parameters; --  Multiplier
   V_Speed_Acc_Fac      : T_Speed := -48.0
     with Part_Of => V_Speed_Parameters; --  Multiplier
   V_Acc_Deadband       : Natural_Float := 0.05
     with Part_Of => V_Speed_Parameters; --  Vertical acceleration deadband
   V_Speed_ASL_Deadband : Natural_Float := 0.005
     with Part_Of => V_Speed_Parameters; --  Vertical speed based on barometer
                                         --  readings deadband
   V_Speed_Limit        : T_Speed := 0.05
     with Part_Of => V_Speed_Parameters; --  used to Saturate vertical velocity
   V_Bias_Alpha         : T_Alpha := 0.98
     with Part_Of => V_Speed_Parameters; --  Blending factor we use to fuse
                                         --  v_Speed_ASL and v_Speed_Acc

   --  Parameters used to calculate the altitude above see level (ASL)
   Asl_Err_Deadband     : Natural_Float := 0.00
     with Part_Of => Asl_Parameters; --  error (target - altitude) deadband
   Asl_Alpha            : T_Alpha := 0.92
     with Part_Of => Asl_Parameters; --  Short term smoothing
   Asl_Alpha_Long       : T_Alpha := 0.93
     with Part_Of => Asl_Parameters; --  Long term smoothing

   --  Parameters used for the Altitude Hold mode
   Alt_Hold_Err_Max     : T_Alpha := 1.0
     with Part_Of => Alt_Hold_Parameters; --  Max cap on current
                                          --  estimated altitude
                                          --  vs target altitude in meters
   Alt_Hold_Change_SENS : T_Sensitivity := 200.0
     with Part_Of => Alt_Hold_Parameters; --  Sensitivity of target altitude
                                          --  change (thrust input control)
                                          --  while hovering.
                                          --  Lower = more sensitive
   --  & faster changes
   Alt_Pid_Asl_Fac          : T_Motor_Fac := 13000.0
     with Part_Of => Alt_Hold_Parameters; --  Relates meters asl to thrust
   Alt_Pid_Alpha            : T_Alpha := 0.8
     with Part_Of => Alt_Hold_Parameters; --  PID Smoothing
   Alt_Hold_Min_Thrust      : T_Uint16 := 00000
     with Part_Of => Alt_Hold_Parameters; --  Minimum hover thrust
   Alt_Hold_Base_Thrust     : T_Uint16 := 43000
     with Part_Of => Alt_Hold_Parameters; --  Approximate throttle needed when
                                          --  in perfect hover.
                                          --  More weight / older battery can
                                          --  use a higher value
   Alt_Hold_Max_Thrust  : T_Uint16 := 60000
     with Part_Of => Alt_Hold_Parameters; --  Max altitude hold thrust

   --  Command types used to control each angle
   Roll_Type            : RPY_Type := ANGLE
     with Part_Of => Command_Types;
   Pitch_Type           : RPY_Type := ANGLE
     with Part_Of => Command_Types;
   Yaw_Type             : RPY_Type := RATE
     with Part_Of => Command_Types;

   --  Variables output from each rate PID, and from the Pilot (Thrust)
   Actuator_Thrust : T_Uint16 := 0
     with Part_Of => Actuator_Commands;
   Actuator_Roll   : T_Int16  := 0
     with Part_Of => Actuator_Commands;
   Actuator_Pitch  : T_Int16  := 0
     with Part_Of => Actuator_Commands;
   Actuator_Yaw    : T_Int16  := 0
     with Part_Of => Actuator_Commands;

   --  Variables used to control each motor's power
   Motor_Power_M4  : T_Uint16 := 0
     with Part_Of => Motor_Powers;
   Motor_Power_M2  : T_Uint16 := 0
     with Part_Of => Motor_Powers;
   Motor_Power_M1  : T_Uint16 := 0
     with Part_Of => Motor_Powers;
   Motor_Power_M3  : T_Uint16 := 0
     with Part_Of => Motor_Powers;

   --  Export all of these varaibles from the C part,
   --  so the C part can debug/log them easily
   pragma Export (C, Gyro, "gyro");
   pragma Export (C, Acc, "acc");
   pragma Export (C, Mag, "mag");

   pragma Export (C, Euler_Roll_Actual, "eulerRollActual");
   pragma Export (C, Euler_Pitch_Actual, "eulerPitchActual");
   pragma Export (C, Euler_Yaw_Actual, "eulerYawActual");
   pragma Export (C, Euler_Roll_Desired, "eulerRollDesired");
   pragma Export (C, Euler_Pitch_Desired, "eulerPitchDesired");
   pragma Export (C, Euler_Yaw_Desired, "eulerYawDesired");
   pragma Export (C, Roll_Rate_Desired, "rollRateDesired");
   pragma Export (C, Pitch_Rate_Desired, "pitchRateDesired");
   pragma Export (C, Yaw_Rate_Desired, "yawRateDesired");

   pragma Export (C, Temperature, "temperature");
   pragma Export (C, Pressure, "pressure");
   pragma Export (C, Asl, "asl");
   pragma Export (C, Asl_Raw, "aslRaw");
   pragma Export (C, Asl_Long, "aslLong");

   pragma Export (C, ALT_HOLD_KP, "altHoldKp");
   pragma Export (C, ALT_HOLD_KI, "altHoldKi");
   pragma Export (C, ALT_HOLD_KD, "altHoldKd");
   pragma Export (C, Alt_Hold_PID, "altHoldPID");
   pragma Export (C, Alt_Hold, "altHold");
   pragma Export (C, Set_Alt_Hold, "setAltHold");
   pragma Export (C, Acc_WZ, "accWZ");
   pragma Export (C, Acc_MAG, "accMAG");
   pragma Export (C, V_Speed_ASL, "vSpeedASL");
   pragma Export (C, V_Speed_Acc, "vSpeedAcc");
   pragma Export (C, V_Speed, "vSpeed");
   pragma Export (C, Alt_Hold_PID_Val, "altHoldPIDVal");
   pragma Export (C, Alt_Hold_Err, "altHoldErr");

   pragma Export (C, Alt_Hold_Change, "altHoldChange");
   pragma Export (C, Alt_Hold_Target, "altHoldTarget");
   pragma Export (C, Alt_Hold_Err_Max, "altHoldErrMax");
   pragma Export (C, Alt_Hold_Change_SENS, "altHoldChange_SENS");
   pragma Export (C, Alt_Pid_Asl_Fac, "pidAslFac");
   pragma Export (C, Alt_Pid_Alpha, "pidAlpha");
   pragma Export (C, V_Speed_ASL_Fac, "vSpeedASLFac");
   pragma Export (C, V_Speed_Acc_Fac, "vSpeedAccFac");
   pragma Export (C, V_Acc_Deadband, "vAccDeadband");
   pragma Export (C, V_Speed_ASL_Deadband, "vSpeedASLDeadband");
   pragma Export (C, V_Speed_Limit, "vSpeedLimit");
   pragma Export (C, Asl_Err_Deadband, "errDeadband");
   pragma Export (C, V_Bias_Alpha, "vBiasAlpha");
   pragma Export (C, Asl_Alpha, "aslAlpha");
   pragma Export (C, Asl_Alpha_Long, "aslAlphaLong");

   pragma Export (C, Alt_Hold_Min_Thrust, "altHoldMinThrust");
   pragma Export (C, Alt_Hold_Base_Thrust, "altHoldBaseThrust");
   pragma Export (C, Alt_Hold_Max_Thrust, "altHoldMaxThrust");

   pragma Export (C, Actuator_Thrust, "actuatorThrust");
   pragma Export (C, Actuator_Roll, "actuatorRoll");
   pragma Export (C, Actuator_Pitch, "actuatorPitch");
   pragma Export (C, Actuator_Yaw, "actuatorYaw");

   pragma Export (C, Roll_Type, "rollType");
   pragma Export (C, Pitch_Type, "pitchType");
   pragma Export (C, Yaw_Type, "yawType");

   pragma Export (C, Motor_Power_M4, "motorPowerM4");
   pragma Export (C, Motor_Power_M2, "motorPowerM2");
   pragma Export (C, Motor_Power_M1, "motorPowerM1");
   pragma Export (C, Motor_Power_M3, "motorPowerM3");

   --  Distribute power to the actuators with the PIDs outputs.
   procedure Stabilizer_Distribute_Power
     (Thrust : T_Uint16;
      Roll   : T_Int16;
      Pitch  : T_Int16;
      Yaw    : T_Int16)
     with
       Global => (Output => Motor_Powers);

   --  Limit the given thrust to the maximum thrust supported by the motors.
   function Limit_Thrust (Value : T_Int32) return T_Uint16;
   pragma Inline (Limit_Thrust);

end Stabilizer_Pack;
