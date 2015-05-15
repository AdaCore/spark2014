package Justifinit
  with SPARK_Mode,
       Abstract_State => State
is
   procedure P (Y : in out Integer)
     with Global => (Input => State);

end Justifinit;
