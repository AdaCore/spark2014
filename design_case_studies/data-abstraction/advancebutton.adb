-- The body of AdvanceButton refines AdvanceButton.State into a state abstraction
-- representing an external input defined in a private child.  The other
-- constituents of AdvanceButton.State are normal variables declared in the
-- body of AdvanceButton.
-- I have used a particular notation to denote that AdvanceButton.Raw represents
-- an external input, but this is not the subject of this case study.
-- The case study is concerned with showing we can have state constituents which
-- are declared in a private child.
-- I have used AdvanceButton.Raw.Inputs in the refinement clause but in the
-- body entities of AdvanceButton.Raw are referenced just using Raw.
-- This is the way it is in current SPARK but it is not really consistent.
-- Perhaps it would be more consistent to be using Raw.Inputs in the refinement
-- clause?
with AdvanceButton.Raw;
package body AdvanceButton
with
Refined_State => (State => ((AdvanceButton.Raw.Inputs => (Volatile => Input)),
                             AdvanceMode,
                             AdvPressed,
                             AdvTimer))
is
   AdvanceMode : AdvanceModes := Slow;
   AdvPressed  : Boolean      := False;
   AdvTimer    : Clock.Times  := 0;

   function CurrentMode return AdvanceModes is (AdvanceMode);

   procedure SetSlowMode
   with
     Refined_Global  => (Output => AdvanceMode),
     Refined_Depends => (AdvanceMode => null)
   is
   begin
      AdvanceMode := Slow;
   end SetSlowMode;

   procedure SetFastMode
   with
     Refined_Global  => (Output => AdvanceMode),
     Refined_Depends => (AdvanceMode => null)
   is
   begin
      AdvanceMode := Fast;
   end SetFastMode;

   procedure JustPressed (Result :    out Boolean)
   with
     Refined_Global =>
       (Input  => (Raw.Inputs,
                   Clock.Ticks),
        In_Out => (AdvPressed,
                   AdvTimer)),
     Refined_Depends =>
       ((Result, AdvPressed) => AdvPressed, Raw.Inputs,
         AdvTimer =>+ (Raw.Inputs, AdvPressed, Clock.Ticks))
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
   with
     Refined_Global =>
       (Inputs  => (Raw.Inputs, Clock.Ticks),
        In_Out  => AdvTimer,
        Output  => AdvPressed),
     Refined_Depends =>
       ((Result, AdvTimer) => (Raw.Inputs,
                               AdvTimer,
                               Period,
                               Clock.Ticks),
         AdvPressed        => Raw.Inputs)
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
   with
     Refined_Global =>
       (Input  => Raw.Inputs,
        Output => AdvPressed),
     Refined_Depends => ((Result, AdvPressed) =>  Raw.Inputs)
    is
      Pressed : Boolean;
   begin
      Raw.Read (Pressed);
      AdvPressed := Pressed;
      Result := not Pressed;
   end NotPressed;

end AdvanceButton;
