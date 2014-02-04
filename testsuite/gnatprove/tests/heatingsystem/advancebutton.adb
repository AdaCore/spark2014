-- Abstract Advance Button Implementation
with AdvanceButton.Raw;

package body AdvanceButton
  with Refined_State => (State => (AdvanceButton.Raw.Inputs,
                                   AdvanceMode,
                                   AdvPressed,
                                   AdvTimer))
is
   AdvanceMode : AdvanceModes := Slow;
   AdvPressed  : Boolean      := False;
   AdvTimer    : Clock.Times  := 0;

   function CurrentMode return AdvanceModes is (AdvanceMode)
     with Refined_Global => AdvanceMode;

   procedure SetSlowMode
     with Refined_Global  => (Output => AdvanceMode),
          Refined_Depends => (AdvanceMode => null)
   is
   begin
      AdvanceMode := Slow;
   end SetSlowMode;

   procedure SetFastMode
     with Refined_Global  => (Output => AdvanceMode),
          Refined_Depends => (AdvanceMode => null)
   is
   begin
      AdvanceMode := Fast;
   end SetFastMode;

   procedure JustPressed (Result :    out Boolean)
     with Refined_Global  => (Input  => (Raw.Inputs,
                                         Clock.Ticks),
                              In_Out => (AdvPressed,
                                         AdvTimer)),
          Refined_Depends => ((Result,
                               AdvPressed) => (AdvPressed,
                                               Raw.Inputs),
                              AdvTimer     =>+ (Raw.Inputs,
                                                AdvPressed,
                                                Clock.Ticks))
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
     with Refined_Global  => (Input  => (Raw.Inputs,
                                         Clock.Ticks),
                              In_Out => AdvTimer,
                              Output => AdvPressed),
          Refined_Depends => ((Result,
                               AdvTimer)  => (Raw.Inputs,
                                              AdvTimer,
                                              Period,
                                              Clock.Ticks),
                              AdvPressed  => Raw.Inputs)
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
     with Refined_Global  => (Input  => Raw.Inputs,
                              Output => AdvPressed),
          Refined_Depends => ((Result,
                               AdvPressed) => Raw.Inputs)
   is
      Pressed : Boolean;
   begin
      Raw.Read (Pressed);
      AdvPressed := Pressed;
      Result := not Pressed;
   end NotPressed;

end AdvanceButton;
