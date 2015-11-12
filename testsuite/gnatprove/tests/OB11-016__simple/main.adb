with Gene;
with Ada.Text_IO;
procedure Main is
   package P is new Gene (X => 0);
begin
   Ada.Text_IO.Put_Line (Integer'Image (P.Sat_Div (10)));
end Main;
