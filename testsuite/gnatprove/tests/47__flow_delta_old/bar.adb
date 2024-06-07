package body Bar with SPARK_Mode is
   procedure Baz (R : in out Rec) is
   begin
      R.X := 0;
   end Baz;
end Bar;
