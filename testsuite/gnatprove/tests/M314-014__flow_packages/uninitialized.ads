package Uninitialized
  with SPARK_Mode,
       Abstract_State => State
is
   procedure Set (Par : in Natural)
     with Global => (Output => State);
end Uninitialized;
