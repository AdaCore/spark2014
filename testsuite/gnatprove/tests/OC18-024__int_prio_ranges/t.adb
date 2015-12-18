with Ada.Real_Time; use Ada.Real_Time;

package body T is

   task body TT1 is
      Wakeup : Time;
   begin
      loop
         Wakeup := Clock;
         Wakeup := Wakeup + Seconds (1);
         delay until Wakeup;
      end loop;
   end;

   task body TT2 is
      Wakeup : Time;
   begin
      loop
         Wakeup := Clock;
         Wakeup := Wakeup + Seconds (1);
         delay until Wakeup;
      end loop;
   end;

end;
