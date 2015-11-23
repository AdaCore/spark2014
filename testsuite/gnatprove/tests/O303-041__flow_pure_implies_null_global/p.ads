package P
  with Pure, SPARK_Mode, Abstract_State => (State with External)
is
   procedure Proc with Global => (In_Out => State);
   procedure Qroc with Import, Global => (In_Out => State);
end P;
