--  For the sake of this example the lights go as follows:
--
--  Vehicles                 Pedestrians
--
--  Green                    Red
--  Yellow                   Red
--  Red                      Green
--  Red and Yellow           Red
--
--  and over and over they go..

with Ada.Real_Time; use Ada.Real_Time;

package Traffic_Lights is

   --  The following type represents the actual lights of the traffic
   --  light. There are three lights for vehicles and two for pedestrians.
   --  When a component is True the corresponding light is On. When a
   --  component is False the corresponding light is Off.
   type Lights_State is record
      Vehicles_Green    : Boolean := False;
      Vehicles_Yellow   : Boolean := False;
      Vehicles_Red      : Boolean := True;
      Pedestrians_Green : Boolean := True;
      Pedestrians_Red   : Boolean := False;
   end record;

   function Valid_Combination (LS : Lights_State) return Boolean;

   subtype Valid_Lights_State is Lights_State
     with Predicate => Valid_Combination (Valid_Lights_State);

   protected Traffic_Light is
      entry Change_Lights;
      procedure Check_Time;

   private
      --  The following holds the time when the last state change occurred.
      Last_State_Change : Time    := Time_First;

      --  The following is a boolean flag that indicates whether or not the
      --  time has arrived to change the state of the traffic light.
      Change_State      : Boolean := False;

      --  The following variable represents the actual lights of the traffic
      --  light. There are three lights for vehicles and two for pedestrians.
      Lights            : Valid_Lights_State;
   end Traffic_Light;

   task Check_The_Time;
   --  This task determines when it's time to change the traffic light.

   task Change_The_Lights;
   --  This task is periodically notified to change the traffic light.

end Traffic_Lights;
