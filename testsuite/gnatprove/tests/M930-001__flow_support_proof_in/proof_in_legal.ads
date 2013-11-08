package Proof_In_Legal
  with SPARK_Mode,
       Abstract_State => State,
       Initializes    => (State, Var)
is
   Var : Integer := 0;

   function Is_OK_To_Increase return Boolean
     with Global => State;

   procedure Increase (X : in out Integer)
     with Global  => (Proof_In => (State,
                                   Var)),
          Depends => (X => X),
          Pre     => Is_OK_To_Increase,
          Post    => Var = Var'Old;
end Proof_In_Legal;
