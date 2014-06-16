package Test
  with Abstract_State => State,
       Initializes    => (State, Proof_Var)
is
   Proof_Var : Boolean := True;

   procedure Rotate (X, Y, Z : in out Integer)
     with Global  => (Proof_In => Proof_Var),
          Depends => (Y => X,
                      Z => Y,
                      X => Z),
          Post    => Proof_Var;

   function Some_Func return Integer
     with Global => State;

   procedure Some_Proc (X : in out Integer)
     with Global => State,
          Post   => X >= Some_Func;
end Test;
