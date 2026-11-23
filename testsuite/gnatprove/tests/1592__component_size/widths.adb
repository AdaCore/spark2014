package body Widths with SPARK_Mode is
   procedure Check is
   begin
      pragma Assert (Four'Size = 64);
      pragma Assert (Four'Component_Size = 16);
   end Check;
end Widths;
