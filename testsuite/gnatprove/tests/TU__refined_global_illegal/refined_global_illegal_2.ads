package Refined_Global_Illegal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   procedure P1 (Par : out Integer)
     --  TU: 8. If a subprogram has a Refined_Global aspect it is used in the
     --  analysis of the subprogram body rather than its Global aspect.
     with Global => (Input => State);


   procedure P2 (Par : out Integer)
     --  TU: 8. If a subprogram has a Refined_Global aspect it is used in the
     --  analysis of the subprogram body rather than its Global aspect.
     with Global => (In_Out => State);
end Refined_Global_Illegal_2;
