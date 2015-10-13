package body Watchdog is

   task body Watchdog_Task is
      T : Float;
   begin
      Turn_Off;
      loop
         Read (T);
         if T > 9000.0 then
            Turn_On;
         else
            Turn_Off;
         end if;
      end loop;
   end Watchdog_Task;

end Watchdog;
