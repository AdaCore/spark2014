with P; use P;
with Ada.Text_IO;

procedure Test_Sqrt is
   X : Integer;
begin
   for N in Sqrt_Domain loop
      X := Sqrt_Von_Neumann (N);
   end loop;
   Ada.Text_IO.Put_Line ("Good");
end Test_Sqrt;
