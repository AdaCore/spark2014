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
is
   type AdvanceModes is (Slow, Fast);
   -- determines rate of advance when button held down

   function CurrentMode return AdvanceModes;

   procedure SetSlowMode;

   procedure SetFastMode;

   procedure JustPressed (Result :    out Boolean);
   -- return True if button pressed now and not pressed before

   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean);
   -- return True if button was pressed before, is still pressed and Period has
   -- elapsed since it last returned true

   procedure NotPressed (Result :    out Boolean);
   -- return True if button is not currently pressed

end AdvanceButton;
