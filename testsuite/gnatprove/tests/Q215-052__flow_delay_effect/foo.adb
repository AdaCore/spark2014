with Ada.Real_Time; use Ada.Real_Time;

package body Foo is

   G : Integer with Atomic, Async_Writers, Async_Readers;

   procedure P (N : Natural)
   with Global => (Input  => Clock_Time,
                   Output => G)
   is
      Tmp : Time := Clock;
   begin
      G := 0;
      for I in 1 .. N loop
         G := I;
         Tmp := Tmp + Seconds (1);

         delay until Tmp;
      end loop;
   end P;

end Foo;
