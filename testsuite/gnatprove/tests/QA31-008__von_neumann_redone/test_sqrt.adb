with P; use P;
with Ada.Text_IO;

procedure Test_Sqrt is
   X : Integer;
begin
--   for N in Sqrt_Domain loop
   X := Sqrt_Von_Neumann16 (2 ** 15 - 1);
   Ada.Text_IO.Put_Line ("X = " & Integer'Image(X));
--   pragma Assert (46341 * 46341 = 0);
   --   end loop;
--   Ada.Text_IO.Put_Line ("Good");
end Test_Sqrt;
