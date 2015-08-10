with Interfaces; use Interfaces;
with Interfaces.C; use Interfaces.C;
with Interfaces.C.Extensions; use Interfaces.C.Extensions;

with Types; use Types;
with IMU_Pack; use IMU_Pack;
with Pid_Parameters; use Pid_Parameters;
with Pid_Pack;
pragma Elaborate_All (Pid_Pack);

package Controller_Pack
with SPARK_Mode,
  Abstract_State => (Attitude_PIDs, Rate_PIDs, Controller_State)
is
   --  PID Generic package initizalization
   package Attitude_Pid is new Pid_Pack
     (T_Degrees'First,
      T_Degrees'Last,
      Float'First / 4.0,
      Float'Last / 4.0,
      MIN_ATTITUDE_COEFF,
      MAX_ATTITUDE_COEFF);

   package Rate_Pid is new Pid_Pack
     (T_Rate'First,
      T_Rate'Last,
      Float'First / 4.0,
      Float'Last / 4.0,
      MIN_RATE_COEFF,
      MAX_RATE_COEFF);

   --  Procedures and functions

   --  Initalize all the PID's needed for the drone.
   procedure Controller_Init
     with
       Global => (Output => (Attitude_PIDs, Rate_PIDs, Controller_State));
   pragma Export (C, Controller_Init, "ada_controllerInit");

   --  Test if the PID's have been initialized.
   function Controller_Test return bool
     with
       Global => (Input => Controller_State);
   pragma Export (C, Controller_Test, "ada_controllerTest");

   --  Update the rate PID's for each axis (Roll, Pitch, Yaw)
   --  given the measured values along each axis and the desired
   --  values retrieved from the corresponding
   --  attitude PID's.
   procedure Controller_Correct_Rate_PID
     (Roll_Rate_Actual   : T_Rate;
      Pitch_Rate_Actual  : T_Rate;
      Yaw_Rate_Actual    : T_Rate;
      Roll_Rate_Desired  : T_Rate;
      Pitch_Rate_Desired : T_Rate;
      Yaw_Rate_Desired   : T_Rate)
     with
       Global => (In_Out => Rate_PIDs);

   --  Update the attitude PID's for each axis given (Roll, Pitch, Yaw)
   --  given the measured values along each axis and the
   --  desired values retrieved from the commander.
   procedure Controller_Correct_Attitude_Pid
     (Euler_Roll_Actual   : T_Degrees;
      Euler_Pitch_Actual  : T_Degrees;
      Euler_Yaw_Actual    : T_Degrees;
      Euler_Roll_Desired  : T_Degrees;
      Euler_Pitch_Desired : T_Degrees;
      Euler_Yaw_Desired   : T_Degrees)
     with
       Global => (In_Out => Attitude_PIDs);

   --  Reset all the PID's error values.
   procedure Controller_Reset_All_Pid
     with
       Global => (In_Out => (Attitude_PIDs, Rate_PIDs));

   --  Get the output of the rate PID's.
   --  Must be called after 'Controller_Correct_Rate_Pid' to update the PID's.
   procedure Controller_Get_Actuator_Output
     (Actuator_Roll  : out T_Int16;
      Actuator_Pitch : out T_Int16;
      Actuator_Yaw   : out T_Int16)
     with
       Global => (Input => Rate_PIDs);

   --  Get the output of the attitude PID's, which will command the rate PID's.
   --  Must be called after 'Controller_Correct_Attitude_Pid' to update
   --  the PID's.
   procedure Controller_Get_Desired_Rate
     (Roll_Rate_Desired  : out Float;
      Pitch_Rate_Desired : out Float;
      Yaw_Rate_Desired   : out Float)
     with
       Global => (Input => Attitude_PIDs);

private

   --  Global variables

   Roll_Pid       : Attitude_Pid.Pid_Object with Part_Of => Attitude_PIDs;
   Pitch_Pid      : Attitude_Pid.Pid_Object with Part_Of => Attitude_PIDs;
   Yaw_Pid        : Attitude_Pid.Pid_Object with Part_Of => Attitude_PIDs;

   Roll_Rate_Pid  : Rate_Pid.Pid_Object with Part_Of => Rate_PIDs;
   Pitch_Rate_Pid : Rate_Pid.Pid_Object with Part_Of => Rate_PIDs;
   Yaw_Rate_Pid   : Rate_Pid.Pid_Object with Part_Of => Rate_PIDs;

   --  Export these variables to log them in the C part
   pragma Export (C, Roll_Pid, "pidRoll");
   pragma Export (C, Pitch_Pid, "pidPitch");
   pragma Export (C, Yaw_Pid, "pidYaw");
   pragma Export (C, Roll_Rate_Pid, "pidRollRate");
   pragma Export (C, Pitch_Rate_Pid, "pidPitchRate");
   pragma Export (C, Yaw_Rate_Pid, "pidYawRate");

   Is_Init : Boolean := False with Part_Of => Controller_State;

end Controller_Pack;
