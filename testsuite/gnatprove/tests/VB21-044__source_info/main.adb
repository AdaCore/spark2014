with Ada.Text_IO;
with GNAT.Source_Info;
procedure Main
  with
    SPARK_Mode => On
is
   Enclosing_Entity_Name : constant String :=
     GNAT.Source_Info.Enclosing_Entity;
begin
   Ada.Text_IO.Put_Line (Enclosing_Entity_Name);
end Main;
