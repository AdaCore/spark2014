-- Navigation tracking of missile
--
-- $Log: nav.adb,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/09/07 20:11:50  adi
-- Added Restart param to Maintain
--
-- Revision 1.1  2003/09/01 19:50:09  adi
-- Initial revision
--
--

with
  if_barometer,
  if_compass,
  If_Ins,
  If_airspeed,
  Measuretypes.Angle_Ops,
  Measuretypes.Angle_Ops.Trig,
  Sensor_History,
  Systemtypes, Systemtypes.Maths,
  cartesian;
package body Nav
  --# own Location_State is head_xy, head_yz, dx, dy, dz, airspeed &
  --#     sensor_state is barometer_ss, compass_ss,
  --#        ins_ss, airspeed_ss;
is
   subtype Integer32 is Systemtypes.Integer32;

   type Sensor_Status is (Unknown, Valid, Failed, Restarted);

   Dx, Dy, Dz,
     Head_Xy, Head_Yz,
     Airspeed : Sensor_History.Measure_History := Sensor_History.Blank_History;
   Barometer_SS : Sensor_Status := unknown;
   Compass_SS   : Sensor_Status := Unknown;
   Ins_SS       : Sensor_Status := unknown;
   Airspeed_SS  : Sensor_Status := unknown;

   ---------------  Sensor updates  -----------------

   -- Handle an airspeed update
   procedure Handle_Airspeed(Restart : in Boolean)
     --# global in if_airspeed.state;
     --#    in out airspeed_ss;
     --#    in out airspeed, clock.time;
     --# derives
     --#  airspeed_ss
     --#  from *,
     --#       restart,
     --#       if_airspeed.state &
     --#  airspeed
     --#  from *,
     --#       clock.time,
     --#       if_airspeed.state,
     --#       airspeed_ss,
     --#       restart &
     --#  clock.time
     --#  from *,
     --#       if_airspeed.state,
     --#       airspeed_ss,
     --#       restart;
   is
      speed_Now : Meter_Per_sec;
      sensor_Valid : Boolean;
   begin
      if Restart then
         If_Airspeed.Get_Speed(Speed => Speed_Now,
                               Valid => sensor_Valid);
         if sensor_Valid then
            airspeed_ss := valid;
            Sensor_History.Update_Speed_Reading(Item => airspeed,
                                                Data => speed_Now);
         else
            -- Not a valid sensor yet but restarting
            Airspeed_Ss := Restarted;
         end if;
      elsif Airspeed_Ss = Valid or Airspeed_ss = restarted then
         If_airspeed.Get_speed(Speed => Speed_Now,
                               Valid => sensor_Valid);
         if sensor_Valid then
            Sensor_History.Update_Speed_Reading(Item => airspeed,
                                                Data => speed_Now);
         else
            -- Whoops, gone invalid
            airspeed_Ss := Failed;
         end if;
      else
         -- Not restarting, sensor not valid so ignore
         null;
      end if;
   end Handle_airspeed;

   -- Handle a barometer update
   procedure Handle_Barometer(Restart : in Boolean)
     --# global in if_barometer.state;
     --#    in out barometer_ss;
     --#    in out dz, clock.time;
     --# derives
     --#  barometer_ss
     --#  from *,
     --#       restart,
     --#       if_barometer.state &
     --#  dz
     --#  from *,
     --#       clock.time,
     --#       if_barometer.state,
     --#       barometer_ss,
     --#       restart &
     --#  clock.time
     --#  from *,
     --#       if_barometer.state,
     --#       barometer_ss,
     --#       restart;
   is
      Height_Now : Meter;
      Baro_Valid : Boolean;
   begin
      if Restart then
         If_Barometer.Get_Height(Height => Height_Now,
                                 Valid => Baro_Valid);
         if Baro_Valid then
            Barometer_ss := valid;
            Sensor_History.Update_Meter_Reading(Item => Dz,
                                                Data => Height_Now);
         else
            -- Not a valid barometer yet but restarting
            Barometer_Ss := Restarted;
         end if;
      elsif Barometer_Ss = Valid or Barometer_Ss = restarted then
         If_Barometer.Get_Height(Height => Height_Now,
                                 Valid => Baro_Valid);
         if Baro_Valid then
            Sensor_History.Update_Meter_Reading(Item => Dz,
                                                Data => Height_Now);
         else
            -- Whoops, gone invalid
            Barometer_Ss := Failed;
         end if;
      else
         -- Not restarting, barometer not valid so ignore
         null;
      end if;
   end Handle_Barometer;

   -- Handle an INS update
   procedure Handle_Ins(Restart : in Boolean)
     --# global
     --#    in if_ins.state;
     --#    in out ins_ss;
     --#    in out dx, dy, dz, clock.time;
     --# derives
     --#  ins_ss
     --#  from *,
     --#       restart,
     --#       if_ins.state &
     --#  dx, dy, dz
     --#  from *,
     --#       if_ins.state,
     --#       clock.time,
     --#       ins_ss,
     --#       restart &
     --#  clock.time
     --#  from *,
     --#       if_ins.state,
     --#       ins_ss,
     --#       restart;
   is
      Position : Cartesian.Position;
      ins_Valid : Boolean;
   begin
      if Restart then
         If_Ins.Get_Location(Position => Position,
                             Valid => Ins_Valid);
         if ins_Valid then
            ins_ss := valid;
            Sensor_History.Update_Meter_Reading(Item => Dx,
                                                Data => Position.x);
            Sensor_History.Update_Meter_Reading(Item => Dy,
                                                Data => Position.y);
            Sensor_History.Update_Meter_Reading(Item => Dz,
                                                Data => Position.z);
         else
            -- Not a valid ins but restarting
            Ins_Ss := Restarted;
         end if;
      elsif ins_Ss = Valid or ins_Ss = restarted then
         If_Ins.Get_location(Position => Position,
                             Valid => Ins_Valid);
         if ins_Valid then
            Sensor_History.Update_Meter_Reading(Item => Dx,
                           Data => Position.X);
            Sensor_History.Update_Meter_Reading(Item => Dy,
                                                Data => Position.Y);
            Sensor_History.Update_Meter_Reading(Item => Dz,
                                                Data => Position.Z);
         else
            -- Whoops, gone invalid
            Ins_Ss := Failed;
         end if;
      else
         -- Not restarting, device not valid so ignore
         null;
      end if;
   end Handle_Ins;

   -- Handle a compass update
   procedure Handle_compass(Restart : in Boolean)
     --# global
     --#    in if_compass.state;
     --#    in out compass_ss;
     --#    in out head_xy, head_yz, clock.time;
     --# derives
     --#  compass_ss
     --#  from *,
     --#       restart,
     --#       if_compass.state &
     --#  head_xy, head_yz
     --#  from *,
     --#       if_compass.state,
     --#       clock.time,
     --#       compass_ss,
     --#       restart &
     --#  clock.time
     --#  from *,
     --#       if_compass.state,
     --#       compass_ss,
     --#       restart;
   is
      Bearing_Mr_Xy, Bearing_Mr_yz : Measuretypes.Millirad;
      Bearing_Deg : Measuretypes.Angle_Degrees;
      Compass_Valid1, Compass_valid2 : Boolean;
   begin
      if Restart then
         If_compass.Get_XY(Angle => Bearing_Mr_xy,
                           Valid => Compass_Valid1);
         If_compass.Get_YZ(Angle => Bearing_Mr_yz,
                           Valid => compass_Valid2);
         if Compass_Valid1 and Compass_valid2 then
            compass_ss := valid;
            Bearing_Deg := Measuretypes.Angle_Ops.Round_Degree(Bearing_Mr_xy);
            Sensor_History.Update_Angle_Reading(Item => Head_xy,
                                                Data => Bearing_deg);
            Bearing_Deg := Measuretypes.Angle_Ops.Round_Degree(Bearing_Mr_yz);
            Sensor_History.Update_Angle_Reading(Item => Head_yz,
                                                Data => Bearing_deg);
         else
            -- Not a valid ins but restarting
            Compass_Ss := Restarted;
         end if;
      elsif compass_Ss = Valid or compass_Ss = restarted then
         If_compass.Get_XY(Angle => Bearing_Mr_xy,
                           Valid => Compass_Valid1);
         If_compass.Get_YZ(Angle => Bearing_Mr_yz,
                           Valid => compass_Valid2);
         if Compass_Valid1 and Compass_valid2 then
            compass_ss := valid;
            Bearing_Deg := Measuretypes.Angle_Ops.Round_Degree(Bearing_Mr_xy);
            Sensor_History.Update_Angle_Reading(Item => Head_xy,
                                                Data => Bearing_deg);
            Bearing_Deg := Measuretypes.Angle_Ops.Round_Degree(Bearing_Mr_yz);
            Sensor_History.Update_Angle_Reading(Item => Head_yz,
                                                Data => Bearing_deg);
         else
            -- Whoops, gone invalid
            compass_Ss := Failed;
         end if;
      else
         -- Not restarting, device not valid so ignore
         null;
      end if;
   end Handle_Compass;

   ------------------ Public subroutines  --------------------

   procedure Estimate_Height(M : out Meter;
                             C : out confidence)
   --# global in dz, barometer_ss, ins_ss;
   --# derives m,c from barometer_ss, ins_ss, dz;
   is
      T : Clock.Millisecond;
   begin
      case Barometer_Ss is
         when Unknown | Failed | Restarted =>
            -- Try a backup
            if Ins_Ss = Valid then
               -- Secondary sensor valid
               Sensor_History.Get_Recent_Meter(Item => Dz,
                                               Recent => M,
                                               Timestamp => T);
               if (T = 0) then
                  -- Invalid reading
                  C := None;
               else
                  C := Low;
               end if;
            else
               M := 0;
               C := None;
            end if;
         when Valid =>
            Sensor_History.Get_Recent_Meter(Item => Dz,
                                            Recent => M,
                                            Timestamp => T);
            -- Primary sensor valid
            if T = 0 then
               -- invalid reading
               C := None;
            else
               C := High;
            end if;
      end case;
   end Estimate_Height;

   procedure Estimate_Origin_Offset(M : out Meter;
                                    C : out confidence)
     --# global in dx, dy, ins_ss, compass_ss, airspeed_ss;
     --# derives m,c from dx, dy, ins_ss, compass_ss, airspeed_ss;
   is
      Edx, Edy : Meter;
      I_tmp : Integer32;
      T1, T2 : Clock.Millisecond;
   begin
      case Ins_Ss is
         when Unknown | Failed | Restarted =>
            if Compass_Ss = Valid and Airspeed_Ss = Valid then
               -- Add estimation here eventually
               M := 0;
               C := none;
            else
               -- Can't estimate
               M := 0;
               C := none;
            end if;
         when Valid =>
            Sensor_History.Get_Recent_Meter(Item => dx,
                                            Recent => edx,
                                            Timestamp => T1);
            Sensor_History.Get_Recent_Meter(Item => dy,
                                            Recent => edy,
                                            Timestamp => T2);
            -- Primary sensor valid
            if T1 = 0 or T2 = 0 then
               -- invalid reading
               M := 0;
               C := None;
            else
               I_Tmp := (Integer32(Edx) * Integer32(Edx)) +
                 (Integer32(Edy) * Integer32(Edy));
               I_Tmp := Systemtypes.Maths.Sqrt(I_tmp);
               M := Meter(I_Tmp);
               C := High;
            end if;
      end case;
   end Estimate_Origin_Offset;

   procedure Estimate_Heading(A : out Angle_Degrees;
                              C : out Confidence)
   --# global in dx, dy, head_xy, compass_ss, ins_ss;
   --# derives a,c from dx, dy, head_xy, compass_ss, ins_ss;
   is
      T1, T2 : Clock.Millisecond;
      Edx,Edy : Meter;
   begin
      case Compass_Ss is
         when Unknown | Failed | Restarted =>
            if Ins_Ss = Valid then
               -- Read the dx and dy given by Ins
               Sensor_History.Get_Recent_Meter(Item => Dx,
                                               Recent => Edx,
                                               Timestamp => T1);
               Sensor_History.Get_Recent_Meter(Item => Dy,
                                               Recent => Edy,
                                               Timestamp => T2);
               if T1 = 0 or T2 = 0 then
                  -- invalid
                  A := 0;
                  C := None;
               else
                  A := Measuretypes.Angle_Ops.Trig.Arctan2(X => eDx,
                                                           Y => eDy);
                  C := Low;
               end if;
            else
               A := 0;
               C := None;
            end if;
         when Valid =>
            Sensor_History.Get_Recent_Angle(Item => Head_Xy,
                                            Recent => A,
                                            Timestamp => T1);
            if T1 = 0 then
               C := None;
            else
               C := High;
            end if;
      end case;
   end Estimate_Heading;

   procedure Estimate_Speed(S : out Meter_Per_Sec;
                            C : out Confidence)
     --# global in dx, dy, airspeed, airspeed_ss, compass_ss, ins_ss;
     --#   in out clock.time;
   --# derives s,c from dx, dy, airspeed, airspeed_ss, ins_ss,
   --#  compass_ss, clock.time &
     --#  clock.time from *, airspeed_ss;
   is
      T1 : Clock.Millisecond;
      I_Tmp : Integer32;
      M : Meter;
      C_Tmp : Confidence;
      Time_Valid : Boolean;
   begin
      case airspeed_Ss is
         when Unknown | Failed | Restarted =>
            Estimate_Origin_Offset(M => m,
                                   C => C_Tmp);
            Clock.Read(T => T1,
                       Valid => Time_Valid);
            if Time_Valid and C_tmp /= None then
               I_Tmp := Integer32(M);
               -- Estimate speed by distance over time
               I_Tmp := (I_Tmp * 1_000) / Integer32(T1);
               S := Meter_Per_Sec(I_Tmp);
               C := Low;
            else
               s := 0;
               C := None;
            end if;
         when Valid =>
            Sensor_History.Get_Recent_speed(Item => airspeed,
                                            Recent => s,
                                            Timestamp => T1);
            if T1 = 0 then
               C := None;
            else
               C := High;
            end if;
      end case;
   end Estimate_Speed;


   procedure Maintain(Restart : in Boolean)
     --# global
     --#  in
     --#    if_barometer.State,
     --#    if_compass.state,
     --#    if_airspeed.state,
     --#    if_ins.state;
     --#  in out
     --#    dx, dy, dz, airspeed, head_xy, head_yz,
     --#    barometer_ss, ins_ss,
     --#    compass_ss, airspeed_ss,
     --#    clock.time;
     --# derives
     --#  dx, dy
     --# from
     --#     *,
     --#     restart,
     --#     barometer_ss,
     --#     compass_ss,
     --#     ins_ss,
     --#     airspeed_ss,
     --#     if_barometer.state,
     --#     if_compass.state,
     --#     if_airspeed.state,
     --#     clock.time,
     --#     if_ins.state &
     --# dz
     --# from
     --#     *,
     --#     restart,
     --#     barometer_ss,
     --#     compass_ss,
     --#     ins_ss,
     --#     airspeed_ss,
     --#     if_barometer.state,
     --#     if_compass.state,
     --#     if_airspeed.state,
     --#     clock.time,
     --#     if_ins.state &
     --#  head_xy,
     --#  head_yz
     --#  from
     --#     *,
     --#     restart,
     --#     barometer_ss,
     --#     compass_ss,
     --#     airspeed_ss,
     --#     if_barometer.state,
     --#     if_compass.state,
     --#     if_airspeed.state,
     --#     clock.time &
     --#  airspeed
     --#  from
     --#     *,
     --#     restart,
     --#     airspeed_ss,
     --#     if_airspeed.state,
     --#     clock.time &
     --#  barometer_ss
     --#  from
     --#     *,
     --#     restart,
     --#     if_barometer.state &
     --#  ins_ss
     --#  from
     --#     *,
     --#     restart,
     --#     if_ins.state &
     --#  compass_ss
     --#  from
     --#     *,
     --#     restart,
     --#     if_compass.state &
     --#  airspeed_ss
     --#  from
     --#     *,
     --#     restart,
     --#     if_airspeed.state &
     --#  clock.time from
     --#     *,
     --#     restart,
     --#     barometer_ss,
     --#     airspeed_ss,
     --#     ins_ss,
     --#     compass_ss,
     --#     if_barometer.state,
     --#     if_compass.state,
     --#     if_airspeed.state,
     --#     if_ins.state
     --#  ;
   is
   begin
      Handle_Airspeed(Restart);
      Handle_Barometer(Restart);
      Handle_Compass(Restart);
      Handle_Ins(Restart);
   end Maintain;

   procedure Command is separate;
end Nav;
