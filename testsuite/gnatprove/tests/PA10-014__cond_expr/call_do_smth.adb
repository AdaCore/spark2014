with Test; use Test;
with Ada.Text_IO;
procedure Call_Do_Smth is
   X : T;
begin
   Do_Smth (True, X);
   Ada.Text_IO.Put_Line (T'Image (X));
end Call_Do_Smth;
