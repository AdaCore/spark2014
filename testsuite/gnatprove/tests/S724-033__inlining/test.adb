package body Test is

   procedure Foo with
      SPARK_Mode
   is
      X : Natural := 1;
   begin
      pragma Assert (X = 2);
   end Foo;

   procedure Bar with
      SPARK_Mode, Global => null
   is
      X : Natural := 1;
   begin
      pragma Assert (X = 2);
   end Bar;

   procedure Register_Tests is
      Acc1 : access procedure := Foo'Access;
      Acc2 : access procedure := Bar'Access;
   begin
      null;
   end Register_Tests;

end Test;
