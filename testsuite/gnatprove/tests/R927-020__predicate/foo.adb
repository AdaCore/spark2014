pragma SPARK_Mode;
with Ada.Text_IO;
procedure Foo
is
   procedure Loc1 with Pre => True is
      type My_Type is new String
        with Dynamic_Predicate => My_Type'Length > 0;
      Undetected : constant My_Type := "";  --  @PREDICATE_CHECK:FAIL
   begin
      null;
   end;

   procedure Loc2 with Pre => True is
      type My_Type2 is new Natural
        with Dynamic_Predicate => My_Type2 = 42;
      Detected : constant My_Type2 := 23;  --  @PREDICATE_CHECK:FAIL
   begin
      null;
   end;
begin
  Ada.Text_IO.Put_Line ("Hello");
end Foo;
