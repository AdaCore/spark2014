-- Navigation tracking of missile
--
-- $Log: nav.ads,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/09/07 20:11:31  adi
-- Finalised annotations
--
-- Revision 1.5  2003/09/07 19:19:39  adi
-- Added use of systemtypes.maths
--
-- Revision 1.4  2003/09/07 18:44:48  adi
-- Added sensor_history as import
--
-- Revision 1.3  2003/09/04 18:41:45  adi
-- Sorted out annotations and inherits
--
-- Revision 1.2  2003/09/01 19:44:46  adi
-- Proper code to use nav interfaces
--
--

with Measuretypes,Clock,Systemtypes;
use type Clock.Millisecond;
--# inherit if_barometer, if_compass, if_ins, if_airspeed,
--#  measuretypes, systemtypes, cartesian, clock,
--#  measuretypes.angle_ops, measuretypes.angle_ops.trig,
--#  sensor_history, systemtypes.maths;
package Nav
  --# own Location_State, sensor_state;
  --# initializes Location_State, sensor_state;
is
   -- Low confidence is single-source, High is multiple-source
   type Confidence is (None,Low,high);

   subtype Meter is Measuretypes.Meter;
   subtype Meter_Per_Sec is Measuretypes.Meter_Per_Sec;
   subtype Angle_Degrees is Measuretypes.Angle_Degrees;

   procedure Estimate_Height(M : out Meter;
                             C : out confidence);
   --# global in location_state, sensor_state;
   --# derives m,c from location_state, sensor_state;

   procedure Estimate_Origin_Offset(M : out Meter;
                                    C : out confidence);
   --# global in location_state, sensor_state;
   --# derives m,c from location_state, sensor_state;

   procedure Estimate_Heading(A : out Angle_Degrees;
                              C : out Confidence);
   --# global in location_state, sensor_state;
   --# derives a,c from location_state, sensor_state;

   procedure Estimate_Speed(S : out Meter_Per_Sec;
                            C : out Confidence);
   --# global in location_state, sensor_state;
   --#        in out clock.time;
   --# derives s,c from location_state, sensor_state, clock.time &
   --#   clock.time from *, sensor_state;

   procedure Maintain(Restart : in Boolean);
   --# global in
   --#    if_barometer.State,
   --#    if_compass.state,
   --#    if_airspeed.state,
   --#    if_ins.state;
   --#     in out
   --#    clock.time,
   --#    location_state,
   --#    sensor_state;
   --# derives
   --#  location_state
   --#  from *,
   --#       restart,
   --#       clock.time,
   --#       sensor_state,
   --#       if_barometer.state,
   --#       if_compass.state,
   --#       if_airspeed.state,
   --#       if_ins.state &
   --#  sensor_state
   --#  from *,
   --#       restart,
   --#       sensor_state,
   --#       if_barometer.state,
   --#       if_compass.state,
   --#       if_airspeed.state,
   --#       if_ins.state &
   --#  clock.time
   --#  from *,
   --#       restart,
   --#       sensor_state,
   --#       if_barometer.state,
   --#       if_compass.state,
   --#       if_airspeed.state,
   --#       if_ins.state
   --#   ;

   procedure Command;
   --# derives;
end Nav;
