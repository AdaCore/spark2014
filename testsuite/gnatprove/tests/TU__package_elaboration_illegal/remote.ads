package Remote
  with SPARK_Mode,
       Abstract_State => State
is
   Var : Integer;

   procedure Init_State
     with Global => (Output => State);
end Remote;
