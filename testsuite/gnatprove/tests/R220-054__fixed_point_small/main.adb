with Ada.Text_IO; use Ada.Text_IO;
with FP_Test; use FP_Test;

procedure Main is
   A : constant Signal_Type := 1.0;
   B : constant Signal_Type := -2.0;
   C : constant Signal_Type := Add_Signals (A, B);
begin
   Put_Line (Signal_Type'Image(C));
end Main;
