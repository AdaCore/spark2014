package Proof_In_Illegal
  with SPARK_Mode,
       Abstract_State => State
is
   Var : Natural;

   function Error_Derived_From_Proof_In (X : Integer) return Integer
     with Global => (Proof_In => (State,
                                  Var));

   function Warning_Proof_In_Not_Used (X : Integer) return Integer
     with Global => (Proof_In => (State,
                                  Var));
end Proof_In_Illegal;
