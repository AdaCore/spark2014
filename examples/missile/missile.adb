with Nav,Measuretypes,Systemtypes,ibit;
-- Nav units
with If_Barometer, If_Airspeed, If_Compass, If_Ins;
-- Control units
with If_Fuel, If_Fuze, If_Radar, If_Ir, If_Steer,
  If_Motor, If_Destruct, If_Warhead;
package body Missile
is
   type Phase_Stage is (Off, Bit, Boost, Locating, Homing, Shutdown);

   -- States of communicating components
   type Component_Status is record
      Bit_Phase : Ibit.Phase;
   end record;
   Init_Component_Status : constant Component_Status
     := Component_Status'(Bit_Phase => Ibit.off);
   type Component_Array is array(Bc1553.Lru_Name) of
     Component_Status;
   Init_Component_Array : constant Component_Array
     := Component_Array'(others => Init_Component_Status);

   type State_Record is record
      Phase      : Phase_Stage;
      Components : Component_Array;
   end record;

   State : State_Record;

   procedure Init
   is
   begin
      State := State_Record'
        (Phase => Off,
         Components => Init_Component_Array);
   end Init;

   -- Only check barometer and airspeed for now;
   --  add more components in when ibit check function
   --  added to them.
   procedure Check_Ibit(Complete : out Boolean;
                        Passed   : out Boolean)
     --# global in
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
     --#   ;
     --# derives complete, passed from
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
     --#   ;
   is
      Lru_Elts : constant := Bc1553.Lru_Name'Pos(Bc1553.Lru_Name'Last);
      Ibit_Phase : Ibit.Phase;
      Complete_Count, Passed_Count : Integer := 0;
   begin
      for Lru in Bc1553.Lru_Name loop
         case Lru is
            when Bc1553.Barometer =>
               Ibit_Phase := If_Barometer.Get_Ibit_State;
            when Bc1553.Asi =>
               Ibit_Phase := If_Airspeed.Get_Ibit_State;
            when Bc1553.ins =>
               Ibit_Phase := If_ins.Get_Ibit_State;
            when Bc1553.compass =>
               Ibit_Phase := If_compass.Get_Ibit_State;
            when Bc1553.fuel =>
               Ibit_Phase := If_fuel.Get_Ibit_State;
            when Bc1553.fuze =>
               Ibit_Phase := If_fuze.Get_Ibit_State;
            when Bc1553.radar =>
               Ibit_Phase := If_radar.Get_Ibit_State;
            when Bc1553.infrared =>
               Ibit_Phase := If_ir.Get_Ibit_State;
            when Bc1553.fins =>
               Ibit_Phase := If_steer.Get_Ibit_State;
            when Bc1553.motor =>
               Ibit_Phase := If_motor.Get_Ibit_State;
            when Bc1553.destruct =>
               Ibit_Phase := If_destruct.Get_Ibit_State;
            when Bc1553.warhead =>
               Ibit_Phase := If_warhead.Get_Ibit_State;
         end case;
         --# assert ibit_phase in ibit.phase;
         if Ibit_Phase = Ibit.Pass then
           Complete_Count := Complete_Count + 1;
           passed_Count := passed_Count + 1;
         elsif Ibit_Phase = Ibit.Fail then
           Complete_Count := Complete_Count + 1;
         else
           -- Don't increment counts
           null;
         end if;
      end loop;
      --# assert complete_count >= 0 and
      --#        passed_count >= 0;
      if Complete_Count = Lru_elts then
         Complete := True;
         if Passed_Count = Lru_elts then
            Passed := True;
         else
            Passed := False;
         end if;
      else
         Complete := False;
         Passed := False;
      end if;
   end Check_Ibit;

   procedure Poll
   is
      procedure Init_Ibit
        --# global in out state;
        --#   in out
        --#    bus.outputs,
        --#    if_barometer.state,
        --#    if_airspeed.state,
        --#    if_ins.state,
        --#    if_compass.state,
        --#    if_fuel.state,
        --#    if_fuze.state,
        --#    if_radar.state,
        --#    if_ir.state,
        --#    if_steer.state,
        --#    if_motor.state,
        --#    if_destruct.state,
        --#    if_warhead.state;
        --# derives
        --#   state,
        --#    bus.outputs,
        --#    if_barometer.state,
        --#    if_airspeed.state,
        --#    if_ins.state,
        --#    if_compass.state,
        --#    if_fuel.state,
        --#    if_fuze.state,
        --#    if_radar.state,
        --#    if_ir.state,
        --#    if_steer.state,
        --#    if_motor.state,
        --#    if_destruct.state,
        --#    if_warhead.state
        --#  from *;
      is begin
         -- Kick off IBIT on all components
         State.Phase := Bit;
         If_Barometer.Ibit_Start;
         If_Airspeed.Ibit_Start;
         If_Ins.Ibit_Start;
         If_Compass.Ibit_Start;
         If_Fuel.Ibit_Start;
         If_Fuze.Ibit_Start;
         If_Radar.Ibit_Start;
         If_Ir.Ibit_Start;
         If_Steer.Ibit_Start;
         If_Motor.Ibit_Start;
         If_Destruct.Ibit_Start;
         If_Warhead.Ibit_Start;
      end Init_Ibit;

      procedure Manage_Bit_Process
        --# global in
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
        --#   ;
        --#  in out
        --#    clock.time,
        --#    nav.location_state,
        --#    nav.sensor_state,
        --#    state;
        --# derives
        --#  state from
        --#     *,
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
        --#     if_warhead.state &
        --#  clock.time, nav.sensor_state from
        --#     *,
        --#     nav.sensor_state,
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
        --#     if_warhead.state &
        --#   nav.location_state
        --#   from *,
        --#        if_fuel.state,
        --#        if_fuze.state,
        --#        if_radar.state,
        --#        if_ir.state,
        --#        if_steer.state,
        --#        if_motor.state,
        --#        if_destruct.state,
        --#        if_warhead.state,
        --#        if_compass.state,
        --#        if_ins.state,
        --#        if_barometer.state,
        --#        if_airspeed.state,
        --#        nav.sensor_state,
        --#        clock.time
        --#  ;
      is
         Ibit_Complete, Ibit_Passed : Boolean;
      begin
         Check_Ibit(Complete => Ibit_Complete,
                    Passed   => Ibit_Passed);
         if Ibit_Complete then
            if Ibit_Passed then
               -- All (or enough) components are fine
               State.Phase := Boost;
               Nav.Maintain(Restart => True);
            else
               -- Too many have failed; shut down
               State.Phase := Shutdown;
            end if;
         end if;
      end Manage_Bit_Process;

      procedure Manage_Boost_Process
        --# global in
        --#   if_barometer.state,
        --#   if_compass.state,
        --#   if_ins.state,
        --#   if_airspeed.state;
        --#  in out
        --#    clock.time,
        --#    nav.location_state,
        --#    nav.sensor_state,
        --#    state;
        --# derives
        --#  state from
        --#     *,
        --#     nav.location_state,
        --#     nav.sensor_state,
        --#     clock.time,
        --#     if_compass.state,
        --#     if_ins.state,
        --#     if_barometer.state,
        --#     if_airspeed.state &
        --#   clock.time
        --#   from *,
        --#        if_compass.state,
        --#        if_ins.state,
        --#        nav.sensor_state,
        --#        if_barometer.state,
        --#        if_airspeed.state,
        --#        clock.time &
        --#   nav.location_state
        --#   from *,
        --#        if_compass.state,
        --#        if_ins.state,
        --#        if_barometer.state,
        --#        if_airspeed.state,
        --#        nav.sensor_state,
        --#        clock.time &
        --#   nav.sensor_state
        --#   from *,
        --#        if_compass.state,
        --#        if_ins.state,
        --#        if_barometer.state,
        --#        if_airspeed.state,
        --#        nav.sensor_state
        --#  ;
      is
         Est_Height : Measuretypes.Meter;
         Est_Confidence : Nav.Confidence;
      begin
         Nav.Maintain(Restart => False);
         -- Ready to locate when we're reliably 2000m up
         Nav.Estimate_Height(M => Est_Height,
                             C => Est_Confidence);
         if Est_Confidence = Nav.High and then
           Est_Height >= 2_000 then
            State.phase := Locating;
         end if;
      end Manage_Boost_Process;

   begin
      -- Find out where we are
      case State.Phase is
         when Shutdown =>
            -- Do nothing
            null;
         when Off =>
            Init_Ibit;
         when Bit =>
            Manage_Bit_Process;
         when Boost =>
            Manage_Boost_Process;
         when Locating | Homing =>
            Nav.Maintain(Restart => False);
      end case;
   end Poll;

   procedure Command is separate;

end Missile;
