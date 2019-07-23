with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
procedure P (Y : in out Integer) is pragma SPARK_Mode (On);
   type T is range 1 .. 10;
   X : T := 1;
   Unb_Str : Unbounded_String := Null_Unbounded_String;
   Buffer : String (1 .. 10);
   Last : Natural := 10;
begin
   while Last = 10 loop
      Get_Line (Buffer, Last);
      Unb_Str := Unb_Str & Buffer (1 .. Last);
   end loop;
   declare
      S : String := To_String (Unb_Str);
   begin
      Put_Line (T'Image (X));
      X := T'Value (S);
      Put_Line (T'Image (X));
   end;
end P;
