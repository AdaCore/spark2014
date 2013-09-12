with Ada.Text_IO; use Ada.Text_IO;
procedure P (Y : in out Integer) is pragma SPARK_Mode (On);
   type T is range 1 .. 10;
   X : T := 1;
   S : String := Get_Line;
begin
   Put_Line (T'Image (X));
   X := T'Value (S);
   Put_Line (T'Image (X));
end P;

