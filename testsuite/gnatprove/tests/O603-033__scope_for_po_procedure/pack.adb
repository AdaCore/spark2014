with Ada.Real_Time;

package body Pack is

   protected body Store is

      procedure Dummy is
      begin
         null;
         --  Crash happens only with a delay statement here
         delay until Ada.Real_Time.Clock;
      end Dummy;
   end Store;

end Pack;
