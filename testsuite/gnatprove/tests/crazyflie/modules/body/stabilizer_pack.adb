with Interfaces.C; use Interfaces.C;

with Config; use Config;
with Safety_Pack; use Safety_Pack;
with Motors_Pack; use Motors_Pack;
with PM_Pack; use PM_Pack;

package body Stabilizer_Pack
with SPARK_Mode,
  Refined_State => (IMU_Outputs         => (Acc,
                                            Gyro,
                                            Mag),
                    Actual_Angles       => (Euler_Roll_Actual,
                                            Euler_Pitch_Actual,
                                            Euler_Yaw_Actual),
                    Desired_Angles      => (Euler_Roll_Desired,
                                            Euler_Pitch_Desired,
                                            Euler_Yaw_Desired),
                    Desired_Rates       => (Roll_Rate_Desired,
                                            Pitch_Rate_Desired,
                                            Yaw_Rate_Desired),
                    Command_Types       => (Roll_Type,
                                            Pitch_Type,
                                            Yaw_Type),
                    Actuator_Commands   => (Actuator_Thrust,
                                            Actuator_Roll,
                                            Actuator_Pitch,
                                            Actuator_Yaw),
                    Motor_Powers        => (Motor_Power_M1,
                                            Motor_Power_M2,
                                            Motor_Power_M3,
                                            Motor_Power_M4),
                    V_Speed_Parameters  => (V_Speed_ASL_Fac,
                                            V_Speed_Acc_Fac,
                                            V_Acc_Deadband,
                                            V_Speed_ASL_Deadband,
                                            V_Speed_Limit,
                                            V_Bias_Alpha),
                    Asl_Parameters      => (Asl_Err_Deadband,
                                            Asl_Alpha,
                                            Asl_Alpha_Long),
                    Alt_Hold_Parameters => (Alt_Hold_Err_Max,
                                            Alt_Hold_Change_SENS,
                                            Alt_Pid_Asl_Fac,
                                            Alt_Pid_Alpha,
                                            Alt_Hold_Base_Thrust,
                                            Alt_Hold_Min_Thrust,
                                            Alt_Hold_Max_Thrust),
                    V_Speed_Variables   => (Acc_WZ,
                                            Acc_MAG,
                                            V_Speed,
                                            V_Speed_Acc,
                                            V_Speed_ASL),
                    Asl_Variables       => (Temperature,
                                            Pressure,
                                            Asl,
                                            Asl_Raw,
                                            Asl_Long),
                    Alt_Hold_Variables  => (Alt_Hold_PID,
                                            Alt_Hold,
                                            Set_Alt_Hold,
                                            Alt_Hold_PID_Val,
                                            Alt_Hold_Err,
                                            Alt_Hold_Change,
                                            Alt_Hold_Target))
is

   --  Private procedures and functions

   function Limit_Thrust (Value : T_Int32) return T_Uint16 is
      Res : T_Uint16;
   begin
      if Value > T_Int32 (T_Uint16'Last) then
         Res := T_Uint16'Last;
      elsif Value < 0 then
         Res := 0;
      else
         pragma Assert (Value <= T_Int32 (T_Uint16'Last));
         Res := T_Uint16 (Value);
      end if;

      return Res;
   end Limit_Thrust;

   procedure Stabilizer_Distribute_Power
     (Thrust : T_Uint16;
      Roll   : T_Int16;
      Pitch  : T_Int16;
      Yaw    : T_Int16)
   is
      T : constant T_Int32 := T_Int32 (Thrust);
      R : T_Int32 := T_Int32 (Roll);
      P : T_Int32 := T_Int32 (Pitch);
      Y : constant T_Int32 := T_Int32 (Yaw);

   begin
      if QUAD_FORMATION_X then
         R := R / 2;
         P := P / 2;

         Motor_Power_M1 := Limit_Thrust (T - R + P + Y);
         Motor_Power_M2 := Limit_Thrust (T - R - P - Y);
         Motor_Power_M3 := Limit_Thrust (T + R - P + Y);
         Motor_Power_M4 := Limit_Thrust (T + R + P - Y);
      else
         Motor_Power_M1 := Limit_Thrust (T + P + Y);
         Motor_Power_M2 := Limit_Thrust (T - R - Y);
         Motor_Power_M3 := Limit_Thrust (T - P + Y);
         Motor_Power_M4 := Limit_Thrust (T + R - Y);
      end if;

      Motor_Set_Ratio (MOTOR_M1, Motor_Power_M1);
      Motor_Set_Ratio (MOTOR_M2, Motor_Power_M2);
      Motor_Set_Ratio (MOTOR_M3, Motor_Power_M3);
      Motor_Set_Ratio (MOTOR_M4, Motor_Power_M4);
   end Stabilizer_Distribute_Power;

   procedure Stabilizer_Update_Attitude is
   begin
      SensFusion6_Update_Q (Gyro.X, Gyro.Y, Gyro.Z,
                              Acc.X, Acc.Y, Acc.Z,
                              FUSION_UPDATE_DT);
      --  Get Euler angles
      SensFusion6_Get_Euler_RPY (Euler_Roll_Actual,
                                   Euler_Pitch_Actual,
                                   Euler_Yaw_Actual);
      --  Vertical acceleration woithout gravity
      Acc_WZ := SensFusion6_Get_AccZ_Without_Gravity (Acc.X,
                                                        Acc.Y,
                                                        Acc.Z);
      Acc_MAG := (Acc.X * Acc.X) + (Acc.Y * Acc.Y) + (Acc.Z * Acc.Z);

      --  Estimate vertical speed from acceleration and Saturate
      --  it within a limit
      V_Speed := Saturate (V_Speed +
                              Dead_Band (Acc_WZ, V_Acc_Deadband) *
                              FUSION_UPDATE_DT,
                            -V_Speed_Limit,
                            V_Speed_Limit);

      --  Get the rate commands from the roll, pitch, yaw attitude PID's
      Controller_Correct_Attitude_Pid (Euler_Roll_Actual,
                                       Euler_Pitch_Actual,
                                       Euler_Yaw_Actual,
                                       Euler_Roll_Desired,
                                       Euler_Pitch_Desired,
                                       -Euler_Yaw_Desired);
      Controller_Get_Desired_Rate (Roll_Rate_Desired, Pitch_Rate_Desired,
                                   Yaw_Rate_Desired);
   end Stabilizer_Update_Attitude;

   procedure Stabilizer_Update_Rate is
   begin
      --  If CF is in Rate mode, give the angles given by the pilot
      --  as input for the Rate PIDs
      if Roll_Type = RATE then
         Roll_Rate_Desired := Euler_Roll_Desired;
      end if;

      if Pitch_Type = RATE then
         Pitch_Rate_Desired := Euler_Pitch_Desired;
      end if;

      if Yaw_Type = RATE then
         Yaw_Rate_Desired := -Euler_Yaw_Desired;
      end if;

      Controller_Correct_Rate_PID (Gyro.X, -Gyro.Y, Gyro.Z,
                                   Roll_Rate_Desired,
                                   Pitch_Rate_Desired,
                                   Yaw_Rate_Desired);
      Controller_Get_Actuator_Output (Actuator_Roll,
                                      Actuator_Pitch,
                                      Actuator_Yaw);
   end Stabilizer_Update_Rate;

   procedure Stabilizer_Alt_Hold_Update is
      LPS25H_Data_Valid   : Boolean;
      Prev_Integ          : Float;
      Baro_V_Speed        : T_Speed;
      Alt_Hold_PID_Out    : T_Altitude;
      Raw_Thrust          : T_Int16;
   begin
      --  Get altitude hold commands from the pilot
      Commander_Get_Alt_Hold (Alt_Hold, Set_Alt_Hold, Alt_Hold_Change);

      --  Get barometer altitude estimations
      LPS25h_Get_Data (Pressure, Temperature, Asl_Raw, LPS25H_Data_Valid);
      if LPS25H_Data_Valid then
         Asl := Saturate (Asl * Asl_Alpha + Asl_Raw * (1.0 - Asl_Alpha),
                           T_Altitude'First,
                           T_Altitude'Last);
         Asl_Long := Saturate (Asl_Long * Asl_Alpha_Long
                                + Asl_Raw * (1.0 - Asl_Alpha_Long),
                                T_Altitude'First,
                                T_Altitude'Last);
      end if;

      --  Estimate vertical speed based on successive barometer readings
      V_Speed_ASL := Saturate (Dead_Band (Asl - Asl_Long,
                                V_Speed_ASL_Deadband),
                                -V_Speed_Limit, V_Speed_Limit);
      --  Estimate vertical speed based on Acc - fused with baro
      --  to reduce drift
      V_Speed := Saturate (V_Speed * V_Bias_Alpha +
                              V_Speed_ASL * (1.0 - V_Bias_Alpha),
                            -V_Speed_Limit, V_Speed_Limit);
      V_Speed_Acc := V_Speed;

      --  Reset Integral gain of PID controller if being charged
      if PM_Is_Discharging = False then
         Alt_Hold_PID.Integ := 0.0;
      end if;

      --  Altitude hold mode just activated, set target altitude as current
      --  altitude. Reuse previous integral term as a starting point
      if Set_Alt_Hold = True then
         --  Set target altitude to current altitude
         Alt_Hold_Target := Asl;
         --  Cache last integral term for reuse after PID init
         Prev_Integ := Alt_Hold_PID.Integ;

         --  Reset PID controller
         Altitude_Pid.Pid_Init (Alt_Hold_PID,
                                Asl,
                                ALT_HOLD_KP,
                                ALT_HOLD_KP,
                                ALT_HOLD_KD,
                                -DEFAULT_PID_INTEGRATION_LIMIT,
                                DEFAULT_PID_INTEGRATION_LIMIT,
                                ALTHOLD_UPDATE_DT);

         Alt_Hold_PID.Integ := Prev_Integ;

         Altitude_Pid.Pid_Update (Alt_Hold_PID, Asl, False);
         Alt_Hold_PID_Val := Saturate (Altitude_Pid.Pid_Get_Output
                                       (Alt_Hold_PID),
                                       T_Altitude'First,
                                       T_Altitude'Last);
      end if;

      if Alt_Hold = True then
         --  Update the target altitude and the PID
         Alt_Hold_Target := Saturate (Alt_Hold_Target +
                                       Alt_Hold_Change / Alt_Hold_Change_SENS,
                                       T_Altitude'First,
                                       T_Altitude'Last);
         Altitude_Pid.Pid_Set_Desired (Alt_Hold_PID, Alt_Hold_Target);

         --  Compute error (current - target), limit the error
         Alt_Hold_Err := Saturate (Dead_Band (Asl - Alt_Hold_Target,
                                    Asl_Err_Deadband),
                                    -Alt_Hold_Err_Max,
                                    Alt_Hold_Err_Max);

         --  Update the Altitude PID
         Altitude_Pid.Pid_Set_Error (Alt_Hold_PID, -Alt_Hold_Err);
         Altitude_Pid.Pid_Update (Alt_Hold_PID, Asl, False);

         Baro_V_Speed := Saturate ((1.0 - Alt_Pid_Alpha)
                                   * ((V_Speed_Acc * V_Speed_Acc_Fac)
                                   + (V_Speed_ASL * V_Speed_ASL_Fac)),
                                   T_Speed'First,
                                   T_Speed'Last);
         Alt_Hold_PID_Out := Saturate (Altitude_Pid.Pid_Get_Output
                                       (Alt_Hold_PID),
                                       T_Altitude'First,
                                       T_Altitude'Last);

         Alt_Hold_PID_Val := Saturate (Alt_Pid_Alpha * Alt_Hold_PID_Val +
                                         Baro_V_Speed + Alt_Hold_PID_Out,
                                       T_Altitude'First,
                                       T_Altitude'Last);

         Raw_Thrust := Truncate_To_T_Int16
           (Alt_Hold_PID_Val * Alt_Pid_Asl_Fac);
         Actuator_Thrust := Saturate (Limit_Thrust (T_Int32 (Raw_Thrust)
                                       + T_Int32 (Alt_Hold_Base_Thrust)),
                                       Alt_Hold_Min_Thrust,
                                       Alt_Hold_Max_Thrust);
      end if;

   end Stabilizer_Alt_Hold_Update;

   --  Public functions

   procedure Stabilizer_Control_Loop
     (Attitude_Update_Counter : in out T_Uint32;
      Alt_Hold_Update_Counter : in out T_Uint32)
   is
   begin
      --  Magnetometer not used for the moment
      IMU_9_Read (Gyro, Acc, Mag);

      --  Do nothing if IMU is not calibrated correctly
      if not IMU_6_Calibrated then
         return;
      end if;

      --  Increment the counters
      Attitude_Update_Counter := Attitude_Update_Counter + 1;
      Alt_Hold_Update_Counter := Alt_Hold_Update_Counter + 1;

      --  Check if the drone is in Free fall or has landed.
      --  This check is enabled by default, but can be disabled
      FF_Check_Event (Acc);

      --  Get commands from the pilot
      Commander_Get_RPY (Euler_Roll_Desired,
                         Euler_Pitch_Desired,
                         Euler_Yaw_Desired);

      Commander_Get_RPY_Type (Roll_Type, Pitch_Type, Yaw_Type);

      --  If FF checks are enabled and the drone is in recovery,
      --  override the pilot commands
      FF_Get_Recovery_Commands (Euler_Roll_Desired,
                                Euler_Pitch_Desired,
                                Roll_Type,
                                Pitch_Type);

      --  Update attitude at IMU_UPDATE_FREQ / ATTITUDE_UPDATE_RATE_DIVIDER
      --  By default the result is 250 Hz
      if Attitude_Update_Counter >= ATTITUDE_UPDATE_RATE_DIVIDER then
         --  Update attitude
         Stabilizer_Update_Attitude;
         --  Reset the counter
         Attitude_Update_Counter := 0;
      end if;

      if IMU_Has_Barometer and
        Alt_Hold_Update_Counter >= ALTHOLD_UPDATE_RATE_DIVIDER
      then
         --  Altidude hold mode update
         Stabilizer_Alt_Hold_Update;
         --  Reset the counter
         Alt_Hold_Update_Counter := 0;
         null;
      end if;

      Stabilizer_Update_Rate;

      if Alt_Hold = False or not IMU_Has_Barometer then
         --  Get thrust from the commander if alt hold mode
         --  not activated
         Commander_Get_Thrust (Actuator_Thrust);
         --  Override the thrust if the drone is in freefall
         FF_Get_Recovery_Thrust (Actuator_Thrust);
      else
         --  Added so thrust can be set to 0 while in altitude hold mode
         --  after disconnect
         Commander_Watchdog;
      end if;

      if Actuator_Thrust > 0 then
         --  Ensure that there is no overflow when changing Yaw sign
         if Actuator_Yaw = T_Int16'First then
            Actuator_Yaw := -T_Int16'Last;
         end if;

         Stabilizer_Distribute_Power (Actuator_Thrust, Actuator_Roll,
                                      Actuator_Pitch, -Actuator_Yaw);
      else
         Stabilizer_Distribute_Power (0, 0, 0, 0);
         Controller_Reset_All_Pid;
      end if;
   end Stabilizer_Control_Loop;

end Stabilizer_Pack;
