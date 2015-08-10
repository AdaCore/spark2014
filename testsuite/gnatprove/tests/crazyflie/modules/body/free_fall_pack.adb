with Safety_Pack; use Safety_Pack;

package body Free_Fall_Pack
with SPARK_Mode,
  Refined_State => (FF_Parameters => (FF_Mode,
                                      FF_DURATION,
                                      LANDING_VARIANCE_THRESHOLD),
                    FF_State      => (FF_Duration_Counter,
                                      In_Recovery,
                                      Recovery_Thrust,
                                      Landing_Data_Collector))
is

   procedure FF_Detect_Free_Fall
     (Acc         :  Accelerometer_Data;
      FF_Detected : out Boolean) is
   begin
      if Acc.X in Free_Fall_Threshold and
        Acc.Y in Free_Fall_Threshold and
        Acc.Z in Free_Fall_Threshold
      then
         FF_Duration_Counter :=
           Saturate (FF_Duration_Counter + 1,
                     0,
                     FF_DURATION + 1);
      else
         FF_Duration_Counter := 0;
      end if;

      FF_Detected := FF_Duration_Counter >= FF_DURATION;
   end FF_Detect_Free_Fall;

   procedure FF_Detect_Landing (Landing_Detected : out Boolean)
   is
      Variance : Float;
      Mean     : Float;
      pragma Unreferenced (Mean);
   begin
      Landing_Detected := False;

      --  Try to detect landing only if a free fall has
      --  been detected and we still are in recovery mode.
      if In_Recovery = 1 then
         Calculate_Variance_And_Mean (Data_Collector => Landing_Data_Collector,
                                      Variance       => Variance,
                                      Mean           => Mean);

         --  If the acc Z variance is superior to the defined threshold
         --  and if the drone is already in the descending phase,
         --  a landing has been detected.
         if Recovery_Thrust <= MIN_RECOVERY_THRUST
           and Variance > LANDING_VARIANCE_THRESHOLD
         then
            Landing_Detected := True;
         end if;
      end if;
   end FF_Detect_Landing;

   procedure FF_Check_Event (Acc : Accelerometer_Data) is
      Has_Detected_FF  : Boolean;
      Has_Landed       : Boolean;
   begin
      --  Check if FF Detection is disabled
      if FF_Mode = DISABLED then
         In_Recovery := 0;
         return;
      end if;

      --  Add the new accelrometer sample for Z axis.
      Add_Acc_Z_Sample (Acc_Z          => Acc.Z,
                        Data_Collector => Landing_Data_Collector);

      --  Detect if the drone has landed.
      FF_Detect_Landing (Has_Landed);

      if Has_Landed then
         In_Recovery := 0;
      end if;

      --  Detect if the drone is in free fall.
      FF_Detect_Free_Fall (Acc, Has_Detected_FF);

      if In_Recovery = 0 and Has_Detected_FF
      then
         In_Recovery := 1;
         Recovery_Thrust := MAX_RECOVERY_THRUST;
      end if;
   end FF_Check_Event;

   procedure FF_Get_Recovery_Commands
     (Euler_Roll_Desired  : in out Float;
      Euler_Pitch_Desired : in out Float;
      Roll_Type           : in out RPY_Type;
      Pitch_Type          : in out RPY_Type) is
   begin
      --  If not in recovery, keep the original commands
      if In_Recovery = 0 then
         return;
      end if;

      --  If in recovery, try to keep the drone straight
      --  by giving it 0 as roll and pitch angles
      Euler_Roll_Desired := 0.0;
      Euler_Pitch_Desired := 0.0;

      --  We change the command types if the drone is ine RATE mode
      Roll_Type := ANGLE;
      Pitch_Type := ANGLE;
   end FF_Get_Recovery_Commands;

   procedure FF_Get_Recovery_Thrust (Thrust : in out T_Uint16) is
   begin
      --  If not in recovery, keep the original thrust
      --  If the pilot has moved his joystick, the drone is not in recovery
      --  anymore
      if In_Recovery = 0 or Thrust > 0 then
         In_Recovery := 0;
         return;
      end if;

      --  If in recovery, decrement the thrust every time this function
      --  is called (In the stabilizer loop)
      Thrust := Recovery_Thrust;
      if Recovery_Thrust > MIN_RECOVERY_THRUST then
         Recovery_Thrust := Recovery_Thrust - RECOVERY_THRUST_DECREMENT;
      end if;
   end FF_Get_Recovery_Thrust;

   procedure Add_Acc_Z_Sample
     (Acc_Z            : T_Acc;
      Data_Collector   : in out FF_Acc_Data_Collector) is
   begin
      Data_Collector.Samples (Data_Collector.Index) := Acc_Z;

      Data_Collector.Index :=
        (Data_Collector.Index mod Data_Collector.Number_Of_Samples) + 1;
   end Add_Acc_Z_Sample;

   procedure Calculate_Variance_And_Mean
     (Data_Collector : FF_Acc_Data_Collector;
      Variance       : out Float;
      Mean           : out Float) is
      Sum        : Float := 0.0;
      Sum_Square : Float := 0.0;
   begin
      for Acc_Z_Sample of Data_Collector.Samples loop
         Sum := Sum + Acc_Z_Sample;
         Sum_Square := Sum_Square + (Acc_Z_Sample * Acc_Z_Sample);
      end loop;

      Mean := Sum / Float (Data_Collector.Number_Of_Samples);
      Variance :=
        (Sum_Square - Sum) / Float (Data_Collector.Number_Of_Samples);
   end Calculate_Variance_And_Mean;

end Free_Fall_Pack;
