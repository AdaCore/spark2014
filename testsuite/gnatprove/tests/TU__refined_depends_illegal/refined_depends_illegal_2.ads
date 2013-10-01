package Refined_Depends_Illegal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   procedure P1 (Par : out Integer)
     --  TU: 8. If a subprogram has a Refined_Depends aspect it is used in the
     --  analysis of the subprogram body rather than its Depends aspect.
     with Depends => (Par => State);


   procedure P2 (Par : Integer)
     --  TU: 8. If a subprogram has a Refined_Depends aspect it is used in the
     --  analysis of the subprogram body rather than its Depends aspect.
     with Global  => (Output => State),
          Depends => (State => Par);
end Refined_Depends_Illegal_2;
