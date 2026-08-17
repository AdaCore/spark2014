with Gen; use Gen;

with Ada.Real_Time; use Ada.Real_Time;

package Inst is

   Now : Time := Clock;
   Start_Time : constant Time := Now;

   procedure P is new Generic_P (T => Time, C => Start_Time);

end;
