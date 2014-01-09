with Early_Init;
with Ada.Integer_Text_IO;
procedure Main is
   X : Positive range 1 .. 100;
begin
   X := Early_Init.Inner_2.V2;
   pragma Assert (X'Valid);
   Ada.Integer_Text_IO.Put (Early_Init.Inner_1.F1 (X));
end Main;
