package body Traffic_Lights is
   function Valid_Combination (LS : Lights_State) return Boolean is
      (if LS.Vehicles_Green then
        not LS.Vehicles_Yellow
        and not LS.Vehicles_Red
        and not LS.Pedestrians_Green
        and LS.Pedestrians_Red

      elsif LS.Pedestrians_Green then
        not LS.Vehicles_Green
        and not LS.Vehicles_Yellow
        and LS.Vehicles_Red
        and not LS.Pedestrians_Red

      else
        not LS.Pedestrians_Green
        and LS.Pedestrians_Red);

   protected body Traffic_Light is

      entry Change_Lights when Change_State is
         LS : Lights_State := Lights;
      begin
         pragma Assume (Valid_Combination (Lights));
         if LS.Vehicles_Green then
            LS.Vehicles_Green  := False;
            LS.Vehicles_Yellow := True;

         elsif LS.Vehicles_Yellow and not LS.Vehicles_Red then
            LS.Vehicles_Yellow   := False;
            LS.Vehicles_Red      := True;
            LS.Pedestrians_Green := True;
            LS.Pedestrians_Red   := False;

         elsif LS.Vehicles_Red and not LS.Vehicles_Yellow then
            LS.Vehicles_Yellow   := True;
            LS.Pedestrians_Green := False;
            LS.Pedestrians_Red   := True;

         elsif LS.Vehicles_Red and LS.Vehicles_Yellow then
            LS.Vehicles_Green  := True;
            LS.Vehicles_Yellow := False;
            LS.Vehicles_Red    := False;
         end if;

         Lights := LS;
         Change_State := False;
         Last_State_Change := Clock;
      end Change_Lights;

      procedure Check_Time is
         Wait_Duration : constant Time_Span :=
           (if Lights.Vehicles_Yellow then
               --  States that involve a yellow vehicle light only last 2
               --  seconds.
               Seconds (2)
            else
               --  All other states last 15 seconds.
               Seconds (15));
         Now : constant Time := Clock;
      begin
         if Now - Last_State_Change >= Wait_Duration then
            --  We have waited enough. It is time for a state change...
            Change_State := True;
         end if;
      end Check_Time;
   end Traffic_Light;

   task body Check_The_Time is
   begin
      loop
         Traffic_Light.Check_Time;
      end loop;
   end Check_The_Time;

   task body Change_The_Lights is
   begin
      loop
         Traffic_Light.Change_Lights;
      end loop;
   end Change_The_Lights;
end Traffic_Lights;
