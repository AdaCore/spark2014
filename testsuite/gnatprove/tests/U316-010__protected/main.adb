with Ada.Text_IO;
with P;

procedure Main with SPARK_Mode => Off is
begin
   for J in 1 .. 10 loop
      Ada.Text_IO.Put_Line (P.PO.F'Image);
   end loop;
end;
