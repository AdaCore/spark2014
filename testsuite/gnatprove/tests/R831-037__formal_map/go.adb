with Ada.Text_IO; use Ada.Text_IO;

with P;

procedure Go  --with SPARK_Mode => Off
is
   M : P.My_Mapping;
   S : String := "hello";
begin

   P.Clear (M);

   if P.Contains (M, S) then
      Put_Line ("Hello World");
   else
      Put_Line ("Eh?");
   end if;

end Go;
