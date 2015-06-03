-- Advance Button Handler
-- The advance button on the control panel has a boundary package like any
-- other hardware interface; however, the kinds of questions we want to ask of
-- this device are more complicated than just "are you pressed?" and this
-- suggests the need for some kind of boundary abstraction layer. The following
-- package provides just such an abstraction and allows more useful questions
-- such as "have you been pressed for 2 seconds?" to be asked. Servicing these
-- questions requires storage of some state information such as the  time in
-- clock ticks when the button is pressed. The raw interface to the advance
-- switch is provided by a private child package whose abstract own variable
-- becomes a refinement constituent of the state of the abstract advance button
-- handler.
-- Abstract Advance Button Interface Package

with Clock;

package AdvanceButton
  -- provides an abstraction of the raw advance button settings
  with Abstract_State => (State with External => Async_Writers),
       Initializes    => State
is
   type AdvanceModes is (Slow, Fast);
   -- determines rate of advance when button held down

   function CurrentMode return AdvanceModes
     with Volatile_Function,
          Global => State;

   procedure SetSlowMode
     with Global  => (In_Out => State),
          Depends => (State => State);

   procedure SetFastMode
     with Global  => (In_Out => State),
          Depends => (State => State);

   procedure JustPressed (Result :    out Boolean)
     with Global  => (Input  => Clock.Ticks,
                      In_Out => State),
          Depends => (Result => State,
                      State  =>+ Clock.Ticks);
   -- return True if button pressed now and not pressed before

   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean)
     with Global  => (Input  => Clock.Ticks,
                      In_Out => State),
          Depends => ((Result,
                       State)  => (Period,
                                   State,
                                   Clock.Ticks));
   -- return True if button was pressed before, is still pressed and Period has
   -- elapsed since it last returned true

   procedure NotPressed (Result :    out Boolean)
     with Global  => (In_Out => State),
          Depends => ((Result,
                       State) => State);
   -- return True if button is not currently pressed

end AdvanceButton;
