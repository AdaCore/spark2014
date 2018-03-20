with Safety_Pack; use Safety_Pack;

package body Free_Fall_Pack
with SPARK_Mode,
  Refined_State => (FF_State      => (FF_Mode,
                                      FF_Duration_Counter,
                                      In_Recovery,
                                      Recovery_Thrust,
                                      Last_Landing_Time,
                                      Last_FF_Detected_Time,
                                      Landing_Data_Collector))
is

   procedure Add_Acc_Z_Sample
     (Acc_Z            : T_Acc;
      Data_Collector   : in out FF_Acc_Data_Collector) is
   begin
      Data_Collector.Samples (Data_Collector.Index) := Acc_Z;

      Data_Collector.Index :=
        (Data_Collector.Index mod Data_Collector.Samples'Last) + 1;
   end Add_Acc_Z_Sample;

   function Calculate_Last_Derivative
     (Data_Collector : FF_Acc_Data_Collector) return Float is
      Last_Sample        : Float
        := Data_Collector.Samples (Data_Collector.Index);
      Penultimate_Sample : Float
        := (if Data_Collector.Index - 1 >= Data_Collector.Samples'First then
               Data_Collector.Samples (Data_Collector.Index - 1)
            else
               Data_Collector.Samples (Data_Collector.Samples'First));
   begin
      return (Last_Sample - Penultimate_Sample);
   end Calculate_Last_Derivative;

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
      Derivative : Float;
   begin
      Landing_Detected := False;

      --  Try to detect landing only if a free fall has
      --  been detected and we still are in recovery mode.
      if In_Recovery = True then

         Derivative := Calculate_Last_Derivative (Landing_Data_Collector);
         --  If the derivative between two samples of the Z acceleration
         --  is superior to the defined threshold
         --  and if the drone is already in the descending phase,
         --  a landing has been detected.
         if Recovery_Thrust <= MIN_RECOVERY_THRUST
           and Derivative > LANDING_DERIVATIVE_THRESHOLD
         then
            Landing_Detected := True;
         end if;
      end if;
   end FF_Detect_Landing;

   procedure FF_Watchdog is
   begin
      --  if the drone is in recovery mode and it has not recovered after
      --  the specified timeout, disable the free fall mode in emergency.
      if In_Recovery = True then
         declare
            Time_Since_Last_Free_Fall : constant Time_Span :=
              Get_Time_Since_Last_Free_Fall;
         begin
            if Time_Since_Last_Free_Fall > RECOVERY_TIMEOUT then
               In_Recovery := False;
               FF_Mode := DISABLED;
            end if;
         end;
      end if;
   end FF_Watchdog;

   procedure FF_Check_Event (Acc : Accelerometer_Data) is
      Has_Detected_FF  : Boolean;
      Has_Landed       : Boolean;
   begin
      --  Check if FF Detection is disabled
      if FF_Mode = DISABLED then
         In_Recovery := False;
         return;
      end if;

      --  Add the new accelrometer sample for Z axis.
      Add_Acc_Z_Sample (Acc_Z          => Acc.Z,
                        Data_Collector => Landing_Data_Collector);

      --  Detect if the drone has landed.
      FF_Detect_Landing (Has_Landed);

      if Has_Landed then
         Last_Landing_Time := Clock;
         In_Recovery := False;
      end if;

      --  Detect if the drone is in free fall.
      FF_Detect_Free_Fall (Acc, Has_Detected_FF);

      if In_Recovery = False and then Has_Detected_FF then
         declare
            Time_Since_Last_Landing : constant Time_Span :=
              Get_Time_Since_Last_Landing;
         begin
            if Time_Since_Last_Landing > STABILIZATION_PERIOD_AFTER_LANDING
            then
               Last_FF_Detected_Time := Clock;
               In_Recovery := True;
               Recovery_Thrust := MAX_RECOVERY_THRUST;
            end if;
         end;
      end if;

      FF_Watchdog;
   end FF_Check_Event;

   procedure FF_Get_Recovery_Commands
     (Euler_Roll_Desired  : in out Float;
      Euler_Pitch_Desired : in out Float;
      Roll_Type           : in out RPY_Type;
      Pitch_Type          : in out RPY_Type) is
   begin
      --  If not in recovery, keep the original commands
      if In_Recovery = False then
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
      if In_Recovery = False or Thrust > 0 then
         In_Recovery := False;
         return;
      end if;

      --  If in recovery, decrement the thrust every time this function
      --  is called (In the stabilizer loop)
      Thrust := Recovery_Thrust;
      if Recovery_Thrust > MIN_RECOVERY_THRUST then
         Recovery_Thrust := Recovery_Thrust - RECOVERY_THRUST_DECREMENT;
      end if;
   end FF_Get_Recovery_Thrust;

   function Get_Time_Since_Last_Landing return Time_Span is
      Now : constant Time := Clock;
   begin
      return Now - Last_Landing_Time;
   end Get_Time_Since_Last_Landing;

   function Get_Time_Since_Last_Free_Fall return Time_Span is
      Now : constant Time := Clock;
   begin
      return Now - Last_FF_Detected_Time;
   end Get_Time_Since_Last_Free_Fall;

end Free_Fall_Pack;
