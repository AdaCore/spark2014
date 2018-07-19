package body E with SPARK_Mode is

   procedure Div is
   begin
      pragma Assert (K /= 0); --@ASSERT:FAIL
      J := 10 / K;
   end Div;
end E;
