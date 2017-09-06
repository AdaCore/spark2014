package body Copy_Values
  with SPARK_Mode
is
   procedure Adjust is
      Cur_Speed : constant Float := Speed;
   begin
      if abs (Cur_Speed) > 100.0 then
         Motor := Motor - 1.0;
      end if;
   end Adjust;

   procedure Smooth is
      Data1 : constant Float := Raw_Data;
      Data2 : constant Float := Raw_Data;
   begin
      Data := Data1;
      Data := (Data1 + Data2) / 2.0;
      Data := Data2;
   end Smooth;

end Copy_Values;
