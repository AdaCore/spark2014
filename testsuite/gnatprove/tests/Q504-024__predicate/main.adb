with Ada.Exceptions;
with Ada.Text_IO;

with Foo;

procedure Main with SPARK_Mode => Off
is
   Value_1, Value_2 : Natural := Natural'First;
begin
   Value_1 := Foo.Get_Elem_1;
   Value_2 := Foo.Get_Elem_2;

exception
   when E : others =>
      Ada.Text_IO.Put_Line
        (Item => Ada.Exceptions.Exception_Information (X => E));
end Main;
