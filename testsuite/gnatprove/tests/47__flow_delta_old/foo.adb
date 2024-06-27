package body Foo with SPARK_Mode is
   procedure Bar (R : in out Rec) is
   begin
      R.X := 0;
   end Bar;
end Foo;
