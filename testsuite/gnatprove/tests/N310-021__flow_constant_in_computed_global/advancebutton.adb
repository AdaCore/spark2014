-- Abstract Advance Button Implementation
with AdvanceButton.Raw;

package body AdvanceButton
is
   AdvanceMode : AdvanceModes := Slow;
   AdvPressed  : Boolean      := False;
   AdvTimer    : Clock.Times  := 0;

   function CurrentMode return AdvanceModes is (AdvanceMode);

   procedure SetSlowMode
   is
   begin
      AdvanceMode := Slow;
   end SetSlowMode;

   procedure SetFastMode
   is
   begin
      AdvanceMode := Fast;
   end SetFastMode;

   procedure JustPressed (Result :    out Boolean)
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
         AdvTimer   := TimePressed;
         Result     := True;
      else
         Result := False;
      end if;
   end JustPressed;


   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean)
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
   is
      Pressed : Boolean;
   begin
      Raw.Read (Pressed);
      AdvPressed := Pressed;
      Result := not Pressed;
   end NotPressed;

end AdvanceButton;
