package body Test with
  SPARK_Mode
is

   procedure Foo (Value : Big_Integer)
   is
   begin
      pragma Assert (0 <= Value);
   end Foo;

   procedure Foo_3 (Value : Big_Integer)
   is
      A : Big_Integer := To_Big_Integer (10_000_000);
      B : Big_Integer := To_Big_Integer (10_000_000);
      C : Big_Integer := To_Big_Integer (10_000_000);
      D : Big_Integer := To_Big_Integer (10_000_000);
   begin
      pragma Assert (A * B * C * D = Value);
   end Foo_3;

   procedure Foo_4 (Value : Big_Integer)
   is
   begin
      pragma Assert (0 <= Value);
   end Foo_4;

end Test;
