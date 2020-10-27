package body Test with
  SPARK_Mode
is

   procedure Foo_2 (Value : Big_Integer)
   is
   begin
      pragma Assert (0 <= Value); --  To big literals are not handled yet
   end Foo_2;

   procedure Foo_5 (Value : Big_Integer)
   is
   begin
      pragma Assert (0 <= Value); --  From_String is only hardcoded on string literals
   end Foo_5;

end Test;
