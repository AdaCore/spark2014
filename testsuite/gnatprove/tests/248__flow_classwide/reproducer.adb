package body Reproducer with
  SPARK_Mode
is

   procedure Foo (Ctx : in out Wrapper) is
   begin
      pragma Assert (Is_Set (Root'Class (Ctx.Inner_Ctx)));
   end Foo;

end Reproducer;
