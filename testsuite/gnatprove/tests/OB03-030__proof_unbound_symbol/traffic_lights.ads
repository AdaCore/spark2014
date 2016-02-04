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
   protected Traffic_Light is
      function Valid_Combination return Boolean;

      entry Change_Lights; --  these contracts are not provable anyway
        --  with Pre  => Valid_Combination,
        --       Post => Valid_Combination;

      procedure Check_Time;
   private
      Last_State_Change : Time    := Time_First;
      Vehicles_Green    : Boolean := False;
      Vehicles_Yellow   : Boolean := False;
      Vehicles_Red      : Boolean := True;
      Pedestrians_Green : Boolean := True;
      Pedestrians_Red   : Boolean := False;
      Change_State      : Boolean := False;
   end Traffic_Light;

   task Check_The_Time;
   --  This task keeps checking the time in order to determine if the state of
   --  the traffic light needs to change.

   task Change_The_Lights;
   --  This tasks keeps checking if the Lights need to be changed, and if
   --  needed, it does so.

end Traffic_Lights;
