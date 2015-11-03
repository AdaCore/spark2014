package body Traffic_Lights is
   protected body Traffic_Light is
      function Valid_Combination return Boolean is
        (Pedestrians_Green = not Pedestrians_Red
           and then Vehicles_Green = not Vehicles_Red
           and then (if Pedestrians_Green then
                       Vehicles_Red and then not Vehicles_Yellow));

      entry Change_Lights when Change_State is
      begin
         Change_State := False;

         if Vehicles_Green then
            Vehicles_Green  := False;
            Vehicles_Yellow := True;

         elsif Vehicles_Yellow
           and then not Vehicles_Red
         then
            Vehicles_Yellow   := False;
            Vehicles_Red      := True;
            Pedestrians_Green := True;
            Pedestrians_Red   := False;

         elsif Vehicles_Red
           and then not Vehicles_Yellow
         then
            Vehicles_Yellow   := True;
            Pedestrians_Green := False;
            Pedestrians_Red   := True;

         elsif Vehicles_Red
           and then Vehicles_Yellow
         then
            Vehicles_Red    := False;
            Vehicles_Yellow := False;
            Vehicles_Green  := True;

         end if;

         Last_State_Change := Clock;
      end Change_Lights;

      procedure Check_Time is
         Wait_Duration : constant Time_Span :=
           (if Vehicles_Yellow then
               Seconds (2)
            else
               Seconds (15));
      begin
         if Clock - Last_State_Change >= Wait_Duration then
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
