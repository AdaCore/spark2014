package Proof_In_Illegal_2
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => State
is
   procedure Error_Derived_From_Proof_In (X : in out Integer)
     with Global => (Proof_In => State);
end Proof_In_Illegal_2;
