package Unit1 with
  SPARK_Mode => Off,
  Abstract_State => State
is
   procedure P with
     Global => (In_Out => State);
end Unit1;
