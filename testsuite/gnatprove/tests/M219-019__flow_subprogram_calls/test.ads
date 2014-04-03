package Test
with SPARK_Mode,
     Abstract_State => State, Initializes => State
is
   procedure Swap_A (X, Y : in out Integer);
   --  Implemented here, without contracts.

   procedure Swap_B (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Implemented here, with contracts.

   procedure Swap_C (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Other.Swap_With_Contract

   procedure Swap_D (X, Y : in out Integer)
   with Depends => (X => Y,                   --  swc messes up precise derives here
                    Y => X);                  --  ditto
   --  Using Other.Swap_Without_Contract

   procedure Swap_E (X, Y : in out Integer)
   with Depends => (X => Y,                   --  no contracts messes up precise derives here
                    Y => X);                  --  ditto
   --  Using Swap_A (no contracts)

   procedure Swap_F (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);
   --  Using Swap_B (contracts)

   procedure Procedure_With_Refinement (X : Integer;
                                        Y : out Integer)
   with Global => (In_Out => State),
        Depends => (State => (State, X),
                    Y     => State);

end Test;
