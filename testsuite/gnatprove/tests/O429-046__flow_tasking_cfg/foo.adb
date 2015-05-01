with Ada.Real_Time; use Ada.Real_Time;

package body Foo
is

   procedure Test_Delay_01
   is
   begin
      delay until Clock + Seconds (5);
   end Test_Delay_01;

end Foo;
