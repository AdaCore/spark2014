
-- Main Control Procedure
with Thermostat,
     Actuator,
     Clock,
     Display,
     Indicator,
     ModeSwitch,
     ProgramSwitch,
     AdvanceButton;
  --# inherit Thermostat,
  --#         Actuator,
  --#         Clock,
  --#         Display,
  --#         Indicator,
  --#         ModeSwitch,
  --#         ProgramSwitch,
  --#         AdvanceButton;
  --# main_program
  procedure HeatingSystem_Proof
  --# global  in     Thermostat.Inputs,
  --#                ModeSwitch.Inputs,
  --#                ProgramSwitch.Inputs,
  --#                Clock.Ticks;
  --#            out Actuator.Outputs,
  --#                Display.Outputs,
  --#                Indicator.Outputs;
  --#         in out AdvanceButton.State;
  --# derives -- Actuator depends on all inputs
  --#         Actuator.Outputs      from    Thermostat.Inputs,
  --#                                       Clock.Ticks,
  --#                                       ProgramSwitch.Inputs,
  --#                                       ModeSwitch.Inputs,
  --#                                       AdvanceButton.State &
  --#         -- Indicator light independent of Thermostat
  --#         Indicator.Outputs     from    Clock.Ticks,
  --#                                       ProgramSwitch.Inputs,
  --#                                       ModeSwitch.Inputs,
  --#                                       AdvanceButton.State &
  --#         -- Digits display not affected by ModeSwitch
  --#         Display.Outputs       from    Clock.Ticks,
  --#                                       ProgramSwitch.Inputs,
  --#                                       AdvanceButton.State &
  --#         -- "less interesting" dependencies
  --#         AdvanceButton.State   from    Clock.Ticks,
  --#                                       ProgramSwitch.Inputs,
  --#                                       AdvanceButton.State;
  is

     HoursInDay      : constant Clock.Times := 24;
     MinutesInHour   : constant Clock.Times := 60;
     SecondsInMinute : constant Clock.Times := 60;
     SecondsInHour   : constant Clock.Times := SecondsInMinute * MinutesInHour;

    subtype ProgramTimes is ProgramSwitch.Positions
      range ProgramSwitch.on1 .. ProgramSwitch.off2;
    type OnOffTimes is array(ProgramTimes) of Clock.Times;

    OnOffTime        : OnOffTimes;
    ClockOffset      : Clock.Times;
    HeatingIsOn      : Boolean;      -- current system setting

    procedure UpdateDisplay (Time : in      Clock.Times)
    --# global  out Display.Outputs;
    --# derives Display.Outputs from Time;
    is

      subtype Hours   is Clock.Times range 0 .. HoursInDay - 1;
      subtype Minutes is Clock.Times range 0 .. MinutesInHour - 1;
      TheDisplay : Display.Displays;
      Hour       : Hours;
      Minute     : Minutes;

    begin --UpdateDisplay
       Hour := Time / SecondsInHour;
       Minute := (Time mod SecondsInHour) / SecondsInMinute;

       TheDisplay := Display.Displays'(Hour / 10,
                                       Hour mod 10,
                                       Minute / 10,
                                       Minute mod 10);
       Display.Write (TheDisplay);
    end UpdateDisplay;

    -----------------------------------------------------------------------------

    procedure CheckAdvanceButton (Time : in out Clock.Times)
    --# global  in     Clock.Ticks;
    --#         in out AdvanceButton.State;
    --# derives Time                  from Time,
    --#                                    Clock.Ticks,
    --#                                    AdvanceButton.State &
    --#         AdvanceButton.State   from Clock.Ticks,
    --#                                    AdvanceButton.State;
    is
       SlowAdvance      : Boolean;
       FastAdvance      : Boolean;
       ChangeToSlowMode : Boolean;
       ChangeToFastMode : Boolean;

    begin --CheckAdvanceButton
       case AdvanceButton.CurrentMode is
          when AdvanceButton.Slow =>
             AdvanceButton.JustPressed (SlowAdvance);
          if SlowAdvance then
             Time := (Time + SecondsInMinute) mod 86400;
          end if;

          AdvanceButton.PressedFor (2, ChangeToFastMode);
          if ChangeToFastMode then
             AdvanceButton.SetFastMode;
          end if;

          when AdvanceButton.Fast =>
             AdvanceButton.PressedFor (1, FastAdvance);
             if FastAdvance then
                Time := (Time + 10 * SecondsInMinute) mod 86400;
             end if;

             AdvanceButton.NotPressed (ChangeToSlowMode);
             if ChangeToSlowMode then
                AdvanceButton.SetSlowMode;
             end if;
       end case;
    end CheckAdvanceButton;

    -----------------------------------------------------------------------------

    -- from Z function AddTime (page 7)
    procedure AddOffset(T : in out Clock.Times)
    --# global in ClockOffset;
    --# derives T from T, ClockOffset;
    --# post T = (T~ + ClockOffset) mod (60 * 60 * 24);
    is
    begin
       T := (T + ClockOffset) mod 86400;
    end AddOffset;

   -----------------------------------------------------------------------------

    procedure CheckProgramSwitch
    --# global  in     Clock.Ticks,
    --#                ProgramSwitch.Inputs;
    --#            out Display.Outputs;
    --#         in out OnOffTime,
    --#                ClockOffset,
    --#                AdvanceButton.State;
    --# derives Display.Outputs       from AdvanceButton.State,
    --#                                    Clock.Ticks,
    --#                                    ClockOffset,
    --#                                    ProgramSwitch.Inputs,
    --#                                    OnOffTime &
    --#         AdvanceButton.State,
    --#         OnOffTime,
    --#         ClockOffset           from *,
    --#                                    AdvanceButton.State,
    --#                                    Clock.Ticks,
    --#                                    ProgramSwitch.Inputs;
    is
       SwitchPosition : ProgramSwitch.Positions;
       Timer          : Clock.Times;

    begin --CheckProgramSwitch
       ProgramSwitch.Read (SwitchPosition);
       case SwitchPosition is
          when ProgramSwitch.auto  =>
             Clock.Read(Timer);
             AddOffset(Timer);

          when ProgramSwitch.clock =>
             Clock.Read (Timer);
             CheckAdvanceButton(ClockOffset);
             AddOffset(Timer);

          when ProgramTimes =>
             Timer := OnOffTime(SwitchPosition);
             CheckAdvanceButton (Timer);
             OnOffTime(SwitchPosition) := Timer;
       end case;

       UpdateDisplay (Timer);
    end CheckProgramSwitch;

    -- from Z function OperatingTimes (page 7)
    function IsBetween(Time, OnTime, OffTime : Clock.Times) return Boolean
    --# return M => (OnTime <= OffTime -> (M <-> (Time > OnTime and Time <  OffTime))) and
    --#             (OnTime >  OffTime -> (M <-> (Time > OnTime or  Time <= OffTime)));
    is
       result : Boolean;
    begin
       if OnTime <= OffTime then
          result := Time > OnTime and Time <  OffTime;
       else
          result := Time > OnTime or  Time <= OffTime;
       end if;
       return result;
    end IsBetween;

    -- Abstraction of check that time is one of the two operating periods.  This is simpler to use
    -- than the full, expanded definition of being in an operating period.  We use a suitable replacement
    -- rule to bind this proof function and the full definition together, thus:
    --
    -- isinoperatingperiod(Ticks, ClockOffset, OnOffTime) may_be_replaced_by
    --                       isbetween((Ticks + ClockOffset) mod 86400,
    --                                  element(OnOffTime, [programswitch__on1]),
    --                                  element(OnOffTime, [programswitch__off1])) or
    --                       isbetween((Ticks + ClockOffset) mod 86400,
    --                                  element(OnOffTime, [programswitch__on2]),
    --                                  element(OnOffTime, [programswitch__off2])).

    --# function IsInOperatingPeriod (TicksNow       : Clock.Times;
    --#                               Offset         : Clock.Times;
    --#                               OperatingTimes : OnOffTimes) return Boolean;
    --# return IsBetween((TicksNow + Offset) mod 86400,
    --#                  OperatingTimes (ProgramSwitch.on1),
    --#                  OperatingTimes (ProgramSwitch.off1)) or
    --#   IsBetween((TicksNow + Offset) mod 86400,
    --#             OperatingTimes (ProgramSwitch.on2),
    --#             OperatingTimes (ProgramSwitch.off2));

    procedure CheckModeSwitch
    --# global  in     Thermostat.Inputs,
    --#                Clock.Ticks,
    --#                ModeSwitch.Inputs,
    --#                OnOffTime,
    --#                ClockOffset;
    --#            out Indicator.Outputs,
    --#                Actuator.Outputs;
    --#         in out HeatingIsOn;
    --# derives Actuator.Outputs,
    --#         HeatingIsOn          from Thermostat.Inputs,
    --#                                   Clock.Ticks,
    --#                                   ModeSwitch.Inputs,
    --#                                   OnOffTime,
    --#                                   ClockOffset,
    --#                                   HeatingIsOn &
    --#         Indicator.Outputs    from Clock.Ticks,
    --#                                   ModeSwitch.Inputs,
    --#                                   OnOffTime,
    --#                                   ClockOffset;

    --# pre   HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs);  -- invariant condition

    --# post (HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs))  -- invariant condition
    --#
    --#      and
    --#
    --# ----------- Mode switch in off position -----------------------Z Schema: +--ModeOff--(page 6)------------
    --#      ((ModeSwitch.Inputs~ = ModeSwitch.off) ->                         --| mode? = off
    --#         (not Indicator.IsOn (Indicator.Outputs) and                    --| Indicator' = isOff
    --#            (not HeatingIsOn) and                                       --| Heating' = isOff
    --#               (not Actuator.IsOn (Actuator.Outputs))))                 --+-------------------------------
    --#
    --#      and
    --#
    --# ----------- Mode switch in continuous position ----------------Z schema: ModeContinuous -(page 7, comprising):
    --#
    --#                                                                        --+--ModeContinuousOp-------------
    --#         ((ModeSwitch.Inputs~ = ModeSwitch.cont) ->                     --| mode? = continuous
    --#            (Indicator.IsOn (Indicator.Outputs)))                       --| Indicator' = isOn
    --#                                                                        --+-------------------------------
    --#      and
    --#                                                                        --+-ModeContinuousOff-------------
    --#         (((ModeSwitch.Inputs~ = ModeSwitch.cont) and                   --| ModeContinuousOp
    --#           Thermostat.RoomTooWarm (Thermostat.Inputs~)) ->              --+------------------
    --#              ((not HeatingIsOn) and                                    --| thermostat? = aboveTemp
    --#                 (not Actuator.IsOn (Actuator.Outputs))))               --| Heating' = IsOff
    --#                                                                        --+-------------------------------
    --#      and
    --#                                                                        --+-ModeCOntinuousOn--------------
    --#         (((ModeSwitch.Inputs~ = ModeSwitch.cont) and                   --| ModeContinuousOp
    --#           not Thermostat.RoomTooWarm (Thermostat.Inputs~)) ->          --+------------------
    --#              (HeatingIsOn and                                          --| thermostat? = belowTemp
    --#                 Actuator.IsOn (Actuator.Outputs)))                     --|  Heating' = IsOn
    --#                                                                        --+-------------------------------
    --#      and
    --#
    --# ----------- Mode switch in timed position ---------------------Z schema: ModeTimed -(page 8, comprising):
    --#
    --#                                                                        --+-ModeTimedPossiblyOn-----------
    --#      (((ModeSwitch.Inputs~ = ModeSwitch.timed) and                     --| mode? = timed
    --#          IsInOperatingPeriod (Clock.Ticks~,                            --| ... in operating period ...
    --#                               ClockOffset,                             --| -- Indicator' = isOn
    --#                               OnOffTime)) ->                           --+-------------------------------
    --#            (Indicator.IsOn (Indicator.Outputs)))
    --#
    --#      and
    --#                                                                        --+-ModeTimedOff------------------
    --#      (((ModeSwitch.Inputs~ = ModeSwitch.timed) and                     --| mode? = timed
    --#         not IsInOperatingPeriod (Clock.Ticks~,                         --| ... not in operating period ...
    --#                                  ClockOffset,                          --| Indicator' = isOff
    --#                                  OnOffTime)) ->                        --| Heating' = isOff
    --#            ((not Indicator.IsOn (Indicator.Outputs)) and               --+-------------------------------
    --#               (not HeatingIsOn) and
    --#                  (not Actuator.IsOn (Actuator.Outputs))))
    --#
    --#      and
    --#                                                                        --+-ModeTimedAboveTemp-------------
    --#      (((ModeSwitch.Inputs~ = ModeSwitch.timed) and                     --| ModeTimedPossiblyOn
    --#          IsInOperatingPeriod (Clock.Ticks~,                            --+--------------------
    --#                               ClockOffset,                             --| thermostat? = aboveTemp
    --#                               OnOffTime) and                           --| Heating' = isOff
    --#             Thermostat.RoomTooWarm (Thermostat.Inputs~)) ->            --+--------------------------------
    --#               ((not HeatingIsOn) and
    --#                  (not Actuator.IsOn (Actuator.Outputs))))
    --#
    --#      and
    --#                                                                        --+-ModeTimedBelowTemp-------------
    --#      (((ModeSwitch.Inputs~ = ModeSwitch.timed) and                     --| ModeTimedPossiblyOn
    --#          IsInOperatingPeriod (Clock.Ticks~,                            --+--------------------
    --#                               ClockOffset,                             --| thermostat? = belowTemp
    --#                               OnOffTime) and                           --| Heating' = isOn
    --#           not Thermostat.RoomTooWarm (Thermostat.Inputs~)) ->          --+--------------------------------
    --#              (HeatingIsOn and
    --#                 Actuator.IsOn (Actuator.Outputs)))
    --#      ;
    is
       MayOperate,
       AboveTemp   : Boolean;
       CurrentTime : Clock.Times;
       ModeSetting : ModeSwitch.Modes;

       procedure TurnOn -- idempotent operation
       --# global  out Actuator.Outputs; in out HeatingIsOn;
       --# derives Actuator.Outputs, HeatingIsOn from HeatingIsOn;
       --# pre  HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs);  -- invariant condition
       --# post (HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs)) -- invariant condition
       --#       and  Actuator.IsOn (Actuator.Outputs);
       is
       begin
          if not HeatingIsOn then
             Actuator.TurnOn;
             HeatingIsOn := True;
          end if;
       end TurnOn;

       procedure TurnOff -- idempotent operation
       --# global  out Actuator.Outputs; in out HeatingIsOn;
       --# derives Actuator.Outputs, HeatingIsOn from HeatingIsOn;
       --# pre  HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs);  -- invariant condition
       --# post (HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs)) -- invariant condition
       --#       and not Actuator.IsOn (Actuator.Outputs);
       is
       begin
          if HeatingIsOn then
             Actuator.TurnOff;
             HeatingIsOn := False;
          end if;
       end TurnOff;




       procedure OperateIfNeeded
       --# global  in     MayOperate,
       --#                AboveTemp;
       --#            out Actuator.Outputs;
       --#            out Indicator.Outputs;
       --#         in out HeatingIsOn;
       --# derives Indicator.Outputs from MayOperate &
       --#         Actuator.Outputs,
       --#         HeatingIsOn       from HeatingIsOn, MayOperate, AboveTemp;

       --# pre  HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs);  -- invariant condition

       --# post (HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs)) -- invariant condition
       --#      and
       --#      (MayOperate -> Indicator.IsOn (Indicator.Outputs)) -- indicator always on when /may/ operate
       --#      and
       --#      ((MayOperate and AboveTemp) ->
       --#         (not Actuator.IsOn (Actuator.Outputs) and       -- too warm, set heating off
       --#            not HeatingIsOn))
       --#      and
       --#      ((MayOperate and not AboveTemp) ->
       --#         (Actuator.IsOn (Actuator.Outputs) and           -- too cold, turn heating on
       --#            HeatingIsOn))
       --#      and
       --#       ((not MayOperate) ->                              -- may not operate, turn everything off
       --#           (not Actuator.IsOn (Actuator.Outputs) and
       --#               not HeatingIsOn and
       --#                  not Indicator.IsOn (Indicator.Outputs)));

       is
       begin -- OperateIfNeeded
            if MayOperate then
               Indicator.TurnOn;
               if AboveTemp then
                    TurnOff;
             else
                  TurnOn;
               end if;
            else
               Indicator.TurnOff;
               TurnOff;
            end if;
       end OperateIfNeeded;


    begin  -- CheckModeSwitch
       ModeSwitch.Read(ModeSetting);
       Clock.Read(CurrentTime);
       AddOffset(CurrentTime);
       Thermostat.AboveTemp(AboveTemp);

       case ModeSetting is
          when ModeSwitch.off   =>
             MayOperate := False;
          when ModeSwitch.cont  =>
             MayOperate := True;
          when ModeSwitch.timed =>
             MayOperate := IsBetween(CurrentTime,
                                     OnOffTime(ProgramSwitch.on1),
                                     OnOffTime(ProgramSwitch.off1)) or else
               IsBetween(CurrentTime,
                         OnOffTime(ProgramSwitch.on2),
                         OnOffTime(ProgramSwitch.off2));
       end case;
       OperateIfNeeded;

    end CheckModeSwitch;

  begin --HeatingSystem
     Actuator.TurnOff;
     Indicator.TurnOff;
     HeatingIsOn := False;
     ClockOffset := 0;
     OnOffTime := OnOffTimes'(ProgramSwitch.on1  => 0,
                              ProgramSwitch.off1 => 0,
                              ProgramSwitch.on2  => 0,
                              ProgramSwitch.off2 => 0);

     loop
        --# assert HeatingIsOn <-> Actuator.IsOn (Actuator.Outputs); -- invariant condition
        CheckProgramSwitch;
        CheckModeSwitch;
     end loop;
  end HeatingSystem_Proof;
