pragma SPARK_Mode;
with Ada.Text_IO;
procedure Foo
is
  type My_Type is new String
  with Dynamic_Predicate => My_Type'Length > 0;
  Undetected : constant My_Type := "";

  type My_Type2 is new Natural
  with Dynamic_Predicate => My_Type2 = 42;
  Detected : constant My_Type2 := 23;
begin
  Ada.Text_IO.Put_Line ("Hello");
end Foo;
