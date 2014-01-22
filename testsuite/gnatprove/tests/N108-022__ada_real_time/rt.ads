with Ada.Real_Time; use Ada.Real_Time;
package RT
  with SPARK_Mode => On
is
   C1 : constant Time := Time_First;
   C2 : constant Time_Span := Tick;

   function F1 return Boolean;

end RT;
