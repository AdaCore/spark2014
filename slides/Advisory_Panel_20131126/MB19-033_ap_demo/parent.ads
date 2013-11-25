package Parent
  with SPARK_Mode
is
   type Switch_Pos is (On, Off, Unknown);
   function Read_Switch return Switch_Pos;
end Parent;
