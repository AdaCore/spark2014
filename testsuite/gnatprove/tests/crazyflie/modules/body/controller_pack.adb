with Safety_Pack; use Safety_Pack;

package body Controller_Pack
with
SPARK_Mode,
  Refined_State => (Attitude_PIDs     => (Roll_Pid,
                                          Pitch_Pid,
                                          Yaw_Pid),
                    Rate_PIDs         => (Roll_Rate_Pid,
                                          Pitch_Rate_Pid,
                                          Yaw_Rate_Pid),
                    Controller_State  =>  Is_Init)
is

   procedure Controller_Init is
   begin
      Rate_Pid.Pid_Init (Roll_Rate_Pid, 0.0, PID_ROLL_RATE_KP,
                         PID_ROLL_RATE_KI, PID_ROLL_RATE_KD,
                         -PID_ROLL_RATE_INTEGRATION_LIMIT,
                         PID_ROLL_RATE_INTEGRATION_LIMIT,
                         IMU_UPDATE_DT);
      Rate_Pid.Pid_Init (Pitch_Rate_Pid, 0.0, PID_PITCH_RATE_KP,
                         PID_PITCH_RATE_KI, PID_PITCH_RATE_KD,
                         -PID_PITCH_RATE_INTEGRATION_LIMIT,
                         PID_PITCH_RATE_INTEGRATION_LIMIT,
                         IMU_UPDATE_DT);
      Rate_Pid.Pid_Init (Yaw_Rate_Pid, 0.0, PID_YAW_RATE_KP,
                         PID_YAW_RATE_KI, PID_YAW_RATE_KD,
                         -PID_YAW_RATE_INTEGRATION_LIMIT,
                         PID_YAW_RATE_INTEGRATION_LIMIT,
                         IMU_UPDATE_DT);

      Attitude_Pid.Pid_Init (Roll_Pid, 0.0, PID_ROLL_KP,
                             PID_ROLL_KI, PID_ROLL_KD,
                             -PID_ROLL_INTEGRATION_LIMIT,
                             PID_ROLL_INTEGRATION_LIMIT,
                             IMU_UPDATE_DT);
      Attitude_Pid.Pid_Init (Pitch_Pid, 0.0, PID_PITCH_KP,
                             PID_PITCH_KI, PID_PITCH_KD,
                             -PID_PITCH_INTEGRATION_LIMIT,
                             PID_PITCH_INTEGRATION_LIMIT,
                             IMU_UPDATE_DT);
      Attitude_Pid.Pid_Init (Yaw_Pid, 0.0, PID_YAW_KP,
                             PID_YAW_KI, PID_YAW_KD,
                             -PID_YAW_INTEGRATION_LIMIT,
                             PID_YAW_INTEGRATION_LIMIT,
                             IMU_UPDATE_DT);


      Is_Init := True;
   end Controller_Init;

   function Controller_Test return bool is
      Res : bool;
   begin
      if Is_Init then
         Res := True;
      else
         Res := False;
      end if;

      return Res;
   end Controller_Test;

   procedure Controller_Correct_Rate_PID (Roll_Rate_Actual   : T_Rate;
                                          Pitch_Rate_Actual  : T_Rate;
                                          Yaw_Rate_Actual    : T_Rate;
                                          Roll_Rate_Desired  : T_Rate;
                                          Pitch_Rate_Desired : T_Rate;
                                          Yaw_Rate_Desired   : T_Rate) is
   begin
      Rate_Pid.Pid_Set_Desired (Roll_Rate_Pid, Roll_Rate_Desired);
      Rate_Pid.Pid_Set_Desired (Pitch_Rate_Pid, Pitch_Rate_Desired);
      Rate_Pid.Pid_Set_Desired (Yaw_Rate_Pid, Yaw_Rate_Desired);

      Rate_Pid.Pid_Update (Pitch_Rate_Pid, Pitch_Rate_Actual, True);
      Rate_Pid.Pid_Update (Roll_Rate_Pid, Roll_Rate_Actual, True);
      Rate_Pid.Pid_Update (Yaw_Rate_Pid, Yaw_Rate_Actual, True);
   end Controller_Correct_Rate_PID;

   procedure Controller_Correct_Attitude_Pid
     (Euler_Roll_Actual   : T_Degrees;
      Euler_Pitch_Actual  : T_Degrees;
      Euler_Yaw_Actual    : T_Degrees;
      Euler_Roll_Desired  : T_Degrees;
      Euler_Pitch_Desired : T_Degrees;
      Euler_Yaw_Desired   : T_Degrees) is
      Yaw_Error : Float := Euler_Yaw_Desired - Euler_Yaw_Actual;
   begin
      Attitude_Pid.Pid_Set_Desired (Roll_Pid, Euler_Roll_Desired);
      Attitude_Pid.Pid_Set_Desired (Pitch_Pid, Euler_Pitch_Desired);

      Attitude_Pid.Pid_Update (Roll_Pid, Euler_Roll_Actual, True);
      Attitude_Pid.Pid_Update (Pitch_Pid, Euler_Pitch_Actual, True);

      --  Special case for Yaw axis
      if Yaw_Error > 180.0 then
         Yaw_Error := Yaw_Error - 360.0;
      elsif Yaw_Error < -180.0 then
         Yaw_Error := Yaw_Error + 360.0;
      end if;

      Attitude_Pid.Pid_Set_Error (Yaw_Pid, Yaw_Error);
      Attitude_Pid.Pid_Update (Yaw_Pid, Euler_Yaw_Actual, False);
   end Controller_Correct_Attitude_Pid;

   procedure Controller_Reset_All_Pid is
   begin
      Rate_Pid.Pid_Reset (Roll_Rate_Pid);
      Attitude_Pid.Pid_Reset (Roll_Pid);
      Rate_Pid.Pid_Reset (Pitch_Rate_Pid);
      Attitude_Pid.Pid_Reset (Pitch_Pid);
      Rate_Pid.Pid_Reset (Yaw_Rate_Pid);
      Attitude_Pid.Pid_Reset (Yaw_Pid);
   end Controller_Reset_All_Pid;

   procedure Controller_Get_Actuator_Output (Actuator_Roll  : out T_Int16;
                                             Actuator_Pitch : out T_Int16;
                                             Actuator_Yaw   : out T_Int16) is
   begin
      Actuator_Roll := Truncate_To_T_Int16
        (Rate_Pid.Pid_Get_Output (Roll_Rate_Pid));
      Actuator_Pitch := Truncate_To_T_Int16
        (Rate_Pid.Pid_Get_Output (Pitch_Rate_Pid));
      Actuator_Yaw := Truncate_To_T_Int16
        (Rate_Pid.Pid_Get_Output (Yaw_Rate_Pid));
   end Controller_Get_Actuator_Output;

   procedure Controller_Get_Desired_Rate (Roll_Rate_Desired  : out Float;
                                          Pitch_Rate_Desired : out Float;
                                          Yaw_Rate_Desired   : out Float) is
   begin
      Roll_Rate_Desired := Attitude_Pid.Pid_Get_Output (Roll_Pid);
      Pitch_Rate_Desired := Attitude_Pid.Pid_Get_Output (Pitch_Pid);
      Yaw_Rate_Desired := Attitude_Pid.Pid_Get_Output (Yaw_Pid);
   end Controller_Get_Desired_Rate;

end Controller_Pack;
