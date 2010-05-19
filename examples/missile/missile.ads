with BC1553,Ibit,Measuretypes,nav;
use type Ibit.Phase;
use type Measuretypes.Meter, Measuretypes.Meter_Per_Sec;
use type Nav.Confidence;
--# inherit
--#  SystemTypes, measuretypes, ibit,
--#  BC1553, clock, bus,
--#  if_airspeed, if_compass, if_ins, if_barometer,
--#  if_fuel, if_fuze, if_radar, if_ir,
--#  if_steer, if_motor, if_destruct, if_warhead,
--#  Nav;
package Missile
  --# own state;
is
   procedure Init;
   --# global out state;
   --# derives state from;

   procedure Poll;
   --# global in out state;
   --#  in out
   --#    clock.time,
   --#    bus.outputs,
   --#    if_airspeed.state,
   --#    if_barometer.state,
   --#    if_compass.state,
   --#    if_destruct.state,
   --#    if_fuel.state,
   --#    if_fuze.state,
   --#    if_ins.state,
   --#    if_ir.state,
   --#    if_motor.state,
   --#    if_radar.state,
   --#    if_steer.state,
   --#    if_warhead.state,
   --#    nav.sensor_state,
   --#    nav.location_state;
   --# derives
   --#   state
   --#   from
   --#     *,
   --#     clock.time,
   --#     if_airspeed.state,
   --#     if_barometer.state,
   --#     if_compass.state,
   --#     if_destruct.state,
   --#     if_fuel.state,
   --#     if_fuze.state,
   --#     if_ins.state,
   --#     if_ir.state,
   --#     if_motor.state,
   --#     if_radar.state,
   --#     if_steer.state,
   --#     if_warhead.state,
   --#     nav.sensor_state,
   --#     nav.location_state &
   --#   clock.time
   --#   from
   --#     *,
   --#     state,
   --#     if_airspeed.state,
   --#     if_compass.state,
   --#     if_ins.state,
   --#     if_barometer.state,
   --#     if_destruct.state,
   --#     if_fuel.state,
   --#     if_fuze.state,
   --#     if_radar.state,
   --#     if_ir.state,
   --#     if_steer.state,
   --#     if_motor.state,
   --#     if_warhead.state,
   --#     nav.sensor_state &
   --#   bus.outputs,
   --#   if_airspeed.state,
   --#   if_barometer.state,
   --#   if_compass.state,
   --#   if_destruct.state,
   --#   if_fuel.state,
   --#   if_fuze.state,
   --#   if_ins.state,
   --#   if_ir.state,
   --#   if_motor.state,
   --#   if_radar.state,
   --#   if_steer.state,
   --#   if_warhead.state
   --#   from
   --#     *,
   --#     state &
   --#   nav.location_state
   --#   from
   --#     *,
   --#     state,
   --#     clock.time,
   --#     if_airspeed.state,
   --#     if_barometer.state,
   --#     if_compass.state,
   --#     if_destruct.state,
   --#     if_fuel.state,
   --#     if_fuze.state,
   --#     if_ins.state,
   --#     if_ir.state,
   --#     if_motor.state,
   --#     if_radar.state,
   --#     if_steer.state,
   --#     if_warhead.state,
   --#     nav.sensor_state &
   --#   nav.sensor_state
   --#   from
   --#     *,
   --#     state,
   --#     if_airspeed.state,
   --#     if_barometer.state,
   --#     if_compass.state,
   --#     if_destruct.state,
   --#     if_fuel.state,
   --#     if_fuze.state,
   --#     if_ins.state,
   --#     if_ir.state,
   --#     if_motor.state,
   --#     if_radar.state,
   --#     if_steer.state,
   --#     if_warhead.state
   --#   ;
   --#

   procedure Command;
   --# derives ;
end Missile;

