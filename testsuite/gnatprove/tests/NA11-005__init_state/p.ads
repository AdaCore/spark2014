package P with
  SPARK_Mode,
  Abstract_State => State
is
   procedure PP with
     Global => (In_Out => State);
end P;
