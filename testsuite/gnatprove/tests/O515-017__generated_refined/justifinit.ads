package Justifinit
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P
     with Global => (Output => State);
end Justifinit;
