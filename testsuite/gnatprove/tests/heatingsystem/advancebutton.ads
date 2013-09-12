-- Advance Button Handler
-- The advance button on the control panel has a boundary package like any other hardware interface;
-- however, the kinds of questions we want to ask of this device are more complicated than just "are you
-- pressed?" and this suggests the need for some kind of boundary abstraction layer.  The following
-- package provides just such an abstraction and allows more useful questions such as "have you been
-- pressed for 2 seconds?" to be asked.  Servicing these questions requires storage of some state
-- information such as the  time in clock ticks when the button is pressed.  The raw interface to
-- the advance switch is provided by a private child package whose abstract own variable becomes
-- a refinement constituent of the state of the abstract advance button handler.
-- Abstract Advance Button Interface Package

with Clock;
--# inherit Clock;
package AdvanceButton -- provides an abstraction of the raw advance button settings
--# own State;
--# initializes State;
is pragma SPARK_Mode (On);
   type AdvanceModes is (Slow, Fast); -- determines rate of advance when button held down

   function CurrentMode return AdvanceModes;
   --# global State;

   procedure SetSlowMode;
   --# global in out State;
   --# derives State from State;

   procedure SetFastMode;
   --# global in out State;
   --# derives State from State;

   procedure JustPressed (Result :    out Boolean);
   --return True if button pressed now and not pressed before
   --# global  in     Clock.Ticks;
   --#         in out State;
   --# derives Result                     from State &
   --#         State                      from State, Clock.Ticks;

   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean);
   --return True if button was pressed before, is still pressed and Period has elapsed
   --since it last returned true
   --# global  in     Clock.Ticks;
   --#         in out State;
   --# derives Result,
   --#         State                from Period,
   --#                                   State,
   --#                                   Clock.Ticks;

   procedure NotPressed (Result :    out Boolean);
   --return True if button is not currently pressed
   --# global  in out State;
   --# derives Result,
   --#         State from State;

end AdvanceButton;
