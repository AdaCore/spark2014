with Foo;
with Bar;

package body Test with
  SPARK_Mode
is

   function Test_Foo return Boolean is
      Context : Foo.Context_Type;
   begin
      Foo.Initialize (Context);
      return Foo.Valid (Context);
   end Test_Foo;

   function Test_Bar return Boolean is
      Context : Foo.Context_Type;
   begin
      Bar.Initialize_Element (Context);
      return Bar.Valid_Element (Context);
   end Test_Bar;

end Test;
