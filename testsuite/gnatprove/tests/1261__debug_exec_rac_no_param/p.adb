with Ada.Text_IO; use Ada.Text_IO;

procedure P with SPARK_Mode is
   X : constant Integer := 15;
begin
   Put_Line ("Starting test");
   Put_Line ("X is " & Integer'Image (X));
   Put_Line ("Done");
end;
