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
   is
   begin
      T := (T + ClockOffset) mod 86400;
   end AddOffset;

   -----------------------------------------------------------------------------

   procedure CheckProgramSwitch
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
   is
      MayOperate,
      AboveTemp   : Boolean;
      CurrentTime : Clock.Times;
      ModeSetting : ModeSwitch.Modes;

      procedure TurnOn -- idempotent operation
      is
      begin
         if not HeatingIsOn then
            Actuator.TurnOn;
            HeatingIsOn := True;
         end if;
      end TurnOn;

      procedure TurnOff -- idempotent operation
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
