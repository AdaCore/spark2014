package Service with
  SPARK_Mode,
  Abstract_State => (State with External)
is
   procedure Extract (Data : out Integer) with
     Global => (In_Out => State);
end Service;
