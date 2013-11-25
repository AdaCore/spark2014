with CC;
with SPARK_IO;

procedure CC_Main
   with SPARK_Mode,
        Global => (In_Out => SPARK_IO.State)
is
   Tomorrow : CC.Days;
begin

   for Today in CC.Days loop
      CC.Next_Day (Today, Tomorrow);
      SPARK_IO.Put_Line (CC.Days'Image(Tomorrow));
   end loop;

end CC_Main;
