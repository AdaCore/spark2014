package Pack
  with SPARK_Mode, Abstract_State => State
is
   function Get return Boolean is (True) with
     Global => (In_Out => State),
     SPARK_Mode => Off;

   function Has return Boolean with
     Global => (In_Out => State),
     SPARK_Mode => Off;

end Pack;
