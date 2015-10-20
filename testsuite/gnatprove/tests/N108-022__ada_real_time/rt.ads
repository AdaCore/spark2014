with Ada.Real_Time; use Ada.Real_Time;

package RT is

   C1 : constant Time := Time_First;
   C2 : constant Time_Span := Tick;

   procedure P1 (X : out Boolean);

end RT;
