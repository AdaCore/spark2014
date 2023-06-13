with Interfaces; use Interfaces;

package body Reproducer with
  SPARK_Mode
is

   procedure Foo (Ctx : Wrapper)
   is
   begin
      pragma Assert (Ctx.Inner_Ctx in Derived); --@ASSERT:PASS
   end Foo;

end Reproducer;
