package body Copy_Values
  with SPARK_Mode
is
   procedure Adjust is
      Cur_Speed : constant F := Speed;
   begin
      if abs (Cur_Speed) > 100.0 then
         Motor := Motor - 1.0;
      end if;
   end Adjust;

end Copy_Values;
