
  with Clock;
  --# inherit Clock;
  package AdvanceButton -- provides an abstraction of the raw advance button settings
  --# own State;
  --# initializes State;
  is

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
     --return TRUE if button pressed now and not pressed before
     --# global  in     Clock.Ticks;
     --#         in out State;
     --# derives Result                     from State &
     --#         State                      from State, Clock.Ticks;

     procedure PressedFor (Period : in     Clock.Times;
                           Result :    out Boolean);
     --return TRUE if button was pressed before, is still pressed and Period
     --has elapsed since it last returned TRUE
     --# global  in     Clock.Ticks;
     --#         in out State;
     --# derives Result,
     --#         State                from Period,
     --#                                   State,
     --#                                   Clock.Ticks;

     procedure NotPressed (Result :    out Boolean);
     --return TRUE if button is not currently pressed
     --# global  in out State;
     --# derives Result,
     --#         State from State;

  end AdvanceButton;
