-- Abstract Advance Button Implementation
with AdvanceButton.Raw;
package body AdvanceButton
--# own State is in AdvanceButton.Raw.Inputs,
--#                 AdvanceMode,
--#                 AdvPressed,
--#                 AdvTimer;
is
   AdvanceMode : AdvanceModes := Slow;
   AdvPressed  : Boolean      := False;
   AdvTimer    : Clock.Times  := 0;

   function CurrentMode return AdvanceModes
   --# global AdvanceMode;
   is
   begin
      return AdvanceMode;
   end CurrentMode;

   procedure SetSlowMode
   --# global out AdvanceMode;
   --# derives AdvanceMode from ;
   is
   begin
      AdvanceMode := Slow;
   end SetSlowMode;

   procedure SetFastMode
   --# global out AdvanceMode;
   --# derives AdvanceMode from ;
   is
   begin
      AdvanceMode := Fast;
   end SetFastMode;

   procedure JustPressed (Result :    out Boolean)
   --# global in     Raw.Inputs;
   --#        in out AdvPressed,
   --#               AdvTimer;
   --#        in     Clock.Ticks;
   --# derives Result,
   --#         AdvPressed  from AdvPressed, Raw.Inputs                 &
   --#         AdvTimer    from *, Raw.Inputs, AdvPressed, Clock.Ticks;
   is
      PressedBefore : Boolean;
      PressedNow    : Boolean;
      TimePressed   : Clock.Times;

   begin
      PressedBefore := AdvPressed;
      Raw.Read (PressedNow);
      Clock.Read (TimePressed);

      if PressedNow and not PressedBefore then
         AdvPressed := True;
         AdvTimer := TimePressed;
         Result := True;
      else
         Result := False;
      end if;
   end JustPressed;


   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean)
   --# global  in     Raw.Inputs, Clock.Ticks;
   --#         in out AdvTimer;
   --#            out AdvPressed;
   --# derives Result,
   --#         AdvTimer     from Raw.Inputs, AdvTimer, Period, Clock.Ticks &
   --#         AdvPressed   from Raw.Inputs;
   is
      StillPressed : Boolean;
      TimeNow      : Clock.Times;

   begin
      Clock.Read (TimeNow);
      Raw.Read (StillPressed);
      AdvPressed := StillPressed;

      if StillPressed then
         if TimeNow - AdvTimer >= Period then
            AdvTimer := AdvTimer + Period;
            Result := True;
         else
            Result := False;
         end if;
      else
         Result := False;
      end if;
   end PressedFor;

   procedure NotPressed (Result :    out Boolean)
   --# global in     Raw.Inputs;
   --#           out AdvPressed;
   --# derives Result,
   --#         AdvPressed from Raw.Inputs;
   is
      Pressed : Boolean;
   begin
      Raw.Read (Pressed);
      AdvPressed := Pressed;
      Result := not Pressed;
   end NotPressed;

end AdvanceButton;
