package body Constants with SPARK_Mode is
   procedure Check is
   begin
      if Value /= null then
         pragma Assert (Value.all in Integer);
      end if;
   end Check;
end Constants;
