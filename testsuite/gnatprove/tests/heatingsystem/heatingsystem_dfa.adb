-- Main Control Procedure
with Thermostat,
     Actuator,
     Clock,
     Display,
     Indicator,
     ModeSwitch,
     ProgramSwitch,
     AdvanceButton;

procedure HeatingSystem_DFA
  with Global  => (Input  => (Thermostat.Inputs,
                              ModeSwitch.Inputs,
                              ProgramSwitch.Inputs,
                              Clock.Ticks),
                   Output => (Actuator.Outputs,
                              Display.Outputs,
                              Indicator.Outputs),
                   In_Out => AdvanceButton.State),

       Depends => (Actuator.Outputs    => (Thermostat.Inputs,
                                           Clock.Ticks,
                                           ProgramSwitch.Inputs,
                                           ModeSwitch.Inputs,
                                           AdvanceButton.State),
                   -- Actuator depends on all inputs
                   Indicator.Outputs   => (Clock.Ticks,
                                           ProgramSwitch.Inputs,
                                           ModeSwitch.Inputs,
                                           AdvanceButton.State),
                   -- Indicator light independent of Thermostat
                   Display.Outputs     => (Clock.Ticks,
                                           ProgramSwitch.Inputs,
                                           AdvanceButton.State),
                   -- Digits display not affected by ModeSwitch
                   AdvanceButton.State => (Clock.Ticks,
                                           ProgramSwitch.Inputs,
                                           AdvanceButton.State))
                   -- "less interesting" dependencies
is
   HoursInDay      : constant Clock.Times := 24;
   MinutesInHour   : constant Clock.Times := 60;
   SecondsInMinute : constant Clock.Times := 60;
   SecondsInHour   : constant Clock.Times := SecondsInMinute * MinutesInHour;

   subtype ProgramTimes is ProgramSwitch.Positions
     range ProgramSwitch.on1 .. ProgramSwitch.off2;
   type OnOffTimes is array(ProgramTimes) of Clock.Times;

   OnOffTime       : OnOffTimes;
   ClockOffset     : Clock.Times;
   HeatingIsOn     : Boolean;      -- current system setting

   procedure UpdateDisplay (Time : in     Clock.Times)
     with Global  => (Output => Display.Outputs),
          Depends => (Display.Outputs => Time)
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
     with Global  => (Input  => Clock.Ticks,
                      In_Out => AdvanceButton.State),
          Depends => (Time                => (Time,
                                              Clock.Ticks,
                                              AdvanceButton.State),
                      AdvanceButton.State => (Clock.Ticks,
                                              AdvanceButton.State))
   is
      SlowAdvance      : Boolean;
      FastAdvance      : Boolean;
      ChangeToSlowMode : Boolean;
      ChangeToFastMode : Boolean;

      CurrentMode : constant AdvanceButton.AdvanceModes :=
        AdvanceButton.CurrentMode;
      --  ??? a workaround for OB27-021: protected calls are not allowed in
      --  case-expressions

   begin --CheckAdvanceButton
      case CurrentMode is
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
     with Global  => ClockOffset,
          Depends => (T => (T,
                            ClockOffset)),
          Post    => T = (T'Old + ClockOffset) mod (60 * 60 * 24)
   is
   begin
      T := (T + ClockOffset) mod 86400;
   end AddOffset;

   -----------------------------------------------------------------------------

   procedure CheckProgramSwitch
     with Global  => (Input  => (Clock.Ticks,
                                 ProgramSwitch.Inputs),
                      Output => Display.Outputs,
                      In_Out => (OnOffTime,
                                 ClockOffset,
                                 AdvanceButton.State)),
          Depends => (Display.Outputs       => (AdvanceButton.State,
                                                Clock.Ticks,
                                                ClockOffset,
                                                ProgramSwitch.Inputs,
                                                OnOffTime),
                      (AdvanceButton.State,
                       OnOffTime,
                       ClockOffset)         =>+ (AdvanceButton.State,
                                                 Clock.Ticks,
                                                 ProgramSwitch.Inputs))
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

   procedure CheckModeSwitch
     with Global  => (Input  => (Thermostat.Inputs,
                                 Clock.Ticks,
                                 ModeSwitch.Inputs,
                                 OnOffTime,
                                 ClockOffset),
                      Output => Indicator.Outputs,
                      In_Out => (Actuator.Outputs,
                                 HeatingIsOn)),
          Depends => (Actuator.Outputs =>+ (Thermostat.Inputs,
                                            Clock.Ticks,
                                            ModeSwitch.Inputs,
                                            OnOffTime,
                                            ClockOffset,
                                            HeatingIsOn),
                      HeatingIsOn       => (Thermostat.Inputs,
                                            Clock.Ticks,
                                            ModeSwitch.Inputs,
                                            OnOffTime,
                                            ClockOffset,
                                            HeatingIsOn),
                      Indicator.Outputs => (Clock.Ticks,
                                            ModeSwitch.Inputs,
                                            OnOffTime,
                                            ClockOffset))
   is
      MayOperate,
      AboveTemp   : Boolean;
      CurrentTime : Clock.Times;
      ModeSetting : ModeSwitch.Modes;

      procedure TurnOn -- idempotent operation
        with Global  => (In_Out => (Actuator.Outputs, HeatingIsOn)),
             Depends => (Actuator.Outputs =>+ HeatingIsOn,
                         HeatingIsOn      => HeatingIsOn)
      is
      begin
         if not HeatingIsOn then
            Actuator.TurnOn;
            HeatingIsOn := True;
         end if;
      end TurnOn;

      procedure TurnOff -- idempotent operation
        with Global  => (In_Out => (Actuator.Outputs, HeatingIsOn)),
             Depends => (Actuator.Outputs =>+ HeatingIsOn,
                         HeatingIsOn      => HeatingIsOn)
      is
      begin
         if HeatingIsOn then
            Actuator.TurnOff;
            HeatingIsOn := False;
         end if;
      end TurnOff;

      -- from Z function OperatingTimes (page 7)
      function IsBetween (Time, OnTime, OffTime : Clock.Times) return Boolean
      is
         (if OnTime <= OffTime
          then Time > OnTime and Time <  OffTime
          else Time > OnTime or  Time <= OffTime);


      procedure OperateIfNeeded
        with Global  => (Input  => (MayOperate,
                                    AboveTemp),
                         Output => Indicator.Outputs,
                         In_Out => (Actuator.Outputs,
                                    HeatingIsOn)),
             Depends => (Indicator.Outputs => MayOperate,
                         Actuator.Outputs  =>+ (HeatingIsOn,
                                                MayOperate,
                                                AboveTemp),
                         HeatingIsOn       =>+ (MayOperate,
                                                AboveTemp))
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
      CheckProgramSwitch;
      CheckModeSwitch;
   end loop;
end HeatingSystem_DFA;
