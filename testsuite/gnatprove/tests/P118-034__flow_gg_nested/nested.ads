package Nested with
   Abstract_State => (State_A,   --  Initialized
                      State_B)   --  Not
is

   procedure State_A_In (X : out Boolean);

   procedure State_A_In_Out;

   procedure State_A_Out;

end Nested;
