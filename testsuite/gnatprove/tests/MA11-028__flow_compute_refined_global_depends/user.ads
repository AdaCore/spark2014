with Lots_Of_Tests; use Lots_Of_Tests;

package User is
   procedure User_Of_No_Contracts (X : out Integer)
     with Global => (State, State2, G1);

   procedure User_Of_G (X, Y : in out Integer)
     with Depends => ((X, Y, State3) => (G1, State, X, Y));

   procedure User_Of_Dep (X : Integer; Y : out Integer)
     with Global => (Input  => (State, State2, State3),
                     Output => G2);

   procedure User_Of_G_D (X : out Integer)
     with Depends => (G2 => G1,
                      X  => State);

   procedure User_Of_RG
     with Depends => (State2 => (G1, State));

   procedure User_Of_RG_D
     with Global  => (Proof_In => State,
                      Input    => (State2, State3),
                      Output   => G1),
          Depends => (G1 => (State2, State3));

   procedure User_Of_RD
     with Global => (Input  => (State2, State3),
                     In_Out => State,
                     Output => G1);

   procedure User_Of_G_RD
     with Depends => (State =>+ (State2, State3));

   procedure User_Of_RG_RD
     with Global  => (In_Out => (G1, State, State3)),
          Depends => (State  =>+ G1,
                      G1     => null,
                      State3 => State3);
end User;
