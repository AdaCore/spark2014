-- This is the AdvanceButton package from the Heating Controller Example
-- from the SPARK SWEWS Course.
-- It has been changed to SPARK 2014 to demonstrate the use of data abstraction
-- where part of the state is within a private child
with Clock;
package AdvanceButton -- provides an abstraction of the raw advance button settings
with
  Abstract_State => State,
  Initial_Condition => State'Defined
is

   type AdvanceModes is (Slow, Fast); -- determines rate of advance when button held down

   function CurrentMode return AdvanceModes
   with
     Global_In => State;

   procedure SetSlowMode
   with
     Global_In_Out => State,
     Derives => (State => State);

   procedure SetFastMode
   with
     Global_In_Out State,
     Derives => (State => State);

   procedure JustPressed (Result :    out Boolean)
   --return TRUE if button pressed now and not pressed before
   with
     Global_In     => Clock.Ticks,
     Global_In_Out => State,
     Derives => (Result => State,
                 State  => (State, Clock.Ticks));

   procedure PressedFor (Period : in     Clock.Times;
                         Result :    out Boolean)
   --return TRUE if button was pressed before, is still pressed and Period
   --has elapsed since it last returned TRUE
   with
     Global_In     => Clock.Ticks,
     Global_In_Out => State,
     Derives => ((Result, State) => (Period, State, Clock.Ticks));

   procedure NotPressed (Result :    out Boolean)
   --return TRUE if button is not currently pressed
   with
     Global_In_Out => State,
     Derives => ((Result, State) => State);

end AdvanceButton;
