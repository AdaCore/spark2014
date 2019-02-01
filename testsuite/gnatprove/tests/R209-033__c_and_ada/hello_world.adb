pragma SPARK_Mode;
with Ada.Text_IO; use Ada.Text_IO;
procedure Hello_World is
   X : Integer := 1;
begin
   Put_Line ("hello, world!");

   for I in 1 .. 10_000 loop
      X := X * X;
      pragma Loop_Invariant (X = 1);
   end loop;
end Hello_World;
