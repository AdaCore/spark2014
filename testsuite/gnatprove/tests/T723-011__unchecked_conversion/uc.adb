with Ada.Unchecked_Conversion;
with Ada.Text_IO;

procedure UC is
   type E is (A, B, C) with Size => 32;
   function Conv is new Ada.Unchecked_Conversion (E, Integer);
   X : E := A;
   Y : Integer := Conv(X);
begin
   Ada.Text_IO.Put_Line (X'Image);
   Ada.Text_IO.Put_Line (Y'Image);   
end UC;
