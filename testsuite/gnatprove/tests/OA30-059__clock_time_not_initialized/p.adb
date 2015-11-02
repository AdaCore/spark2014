with Ada.Real_Time; use type Ada.Real_Time.Time;

package body P is

   procedure Blocking is
   begin
      delay until Ada.Real_Time.Clock;
   end;

end;
