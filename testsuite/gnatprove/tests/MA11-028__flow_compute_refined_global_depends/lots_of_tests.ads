package Lots_Of_Tests
  with Abstract_State => (State, State2, State3),
       Initializes    => (G1, G2, State, State2, State3)
is
   G1, G2 : Integer := 0;

   procedure No_Contracts (X : out Integer);

   procedure Internal_User_Of_No_Contracts_OK (X : out Integer)
     with Depends => (X => (G1, State, State2, State3));

   procedure Internal_User_Of_No_Contracts_BAD (X : out Integer)
     with Depends => (X => (State3, G2));

   procedure G (X, Y : in out Integer)
     with Global => (Input  => (G1, State),
                     Output => State3);

   procedure Internal_User_Of_G_OK (X, Y : in out Integer)
     with Global => (Input => (G1, State));

   procedure Internal_User_Of_G_BAD (X, Y : in out Integer)
     with Global => (Input => (G1, State));

   procedure Dep (X : Integer; Y : out Integer)
     with Depends => (Y  => (X, State3, State2),
                      G2 => State);

   procedure Internal_User_Of_Dep_OK (X : Integer; Y : out Integer)
     with Global => (Input  => (State, State2, State3),
                     Output => G2);

   procedure Internal_User_Of_Dep_BAD (X : Integer; Y : out Integer)
     with Global => (Input  => (State, G1),
                     Output => G2);

   procedure G_D (X : out Integer)
     with Global  => (Input  => (State, G1),
                      Output => G2),
          Depends => (G2 => G1,
                      X  => State);

   procedure Internal_User_Of_G_D_OK (X : out Integer)
     with Global  => (Input  => (State, G1),
                      Output => G2),
          Depends => (G2 => G1,
                      X  => State);

   procedure Internal_User_Of_G_D_BAD (X : out Integer)
     with Depends => (G2 => G1,
                      X  => State);

   procedure RG
     with Global => (Input  => (G1, State),
                     Output => State2);

   procedure Internal_User_Of_RG_OK
     with Depends => (State2 => (State, G1));

   procedure Internal_User_Of_RG_BAD
     with Global  => (Input  => (G1, State),
                      Output => State2);

   procedure RG_D
     with Global  => (Proof_In => State,
                      Input    => (State2, State3),
                      Output   => G1),
          Depends => (G1 => (State2, State3));

   procedure Internal_User_Of_RG_D_OK
     with Global  => (Proof_In => State,
                      Input    => (State2, State3),
                      Output   => G1),
          Depends => (G1 => (State2, State3));

   procedure Internal_User_Of_RG_D_BAD
     with Global  => (Proof_In => State,
                      Input    => (State2, State3),
                      Output   => G1),
          Depends => (G1 => (State2, State3));

   procedure RD
     with Depends => (G1    => (State, State3),
                      State => State2);

   procedure Internal_User_Of_RD_OK
     with Global => (Input  => (State2, State3),
                     In_Out => State,
                     Output => G1);

   procedure Internal_User_Of_RD_BAD
     with Global => (Input  => State3,
                     In_Out => (State, State2),
                     Output => G1);

   procedure G_RD
     with Global  => (Input  => (State2, State3),
                      In_Out => State),
          Depends => (State =>+ (State2, State3));

   procedure Internal_User_Of_G_RD_OK
     with Global  => (Input  => (State2, State3),
                      In_Out => State);

   procedure Internal_User_Of_G_RD_BAD
     with Depends => (State => (State2, State3));

   procedure RG_RD
     with Global  => (In_Out => (G1, State, State3)),
          Depends => (State  =>+ G1,
                      G1     => null,
                      State3 => State3);

   procedure Internal_User_Of_RG_RD_OK
     with Global => (In_Out => (G1, State, State3));

   procedure Internal_User_Of_RG_RD_BAD
     with Global => (In_Out => (G1, State, State3));
end Lots_Of_Tests;
