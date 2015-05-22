with Ada.Real_Time; use Ada.Real_Time;

package body Foo
is

   B : Boolean := False;

   task Test_Task_01;

   task body Test_Task_01 is
   begin
      loop
         B := not B;
      end loop;
   end Test_Task_01;

   procedure Test_Delay_01
   is
   begin
      delay until Clock + Seconds (5);
   end Test_Delay_01;



end Foo;
