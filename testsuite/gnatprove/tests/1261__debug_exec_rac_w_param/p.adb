with Ada.Text_IO; use Ada.Text_IO;

procedure P (X : Integer := 15) with SPARK_Mode is
begin
   Put_Line ("Starting test");
   Put_Line ("X is " & Integer'Image (X));
   Put_Line ("Done");
end;
