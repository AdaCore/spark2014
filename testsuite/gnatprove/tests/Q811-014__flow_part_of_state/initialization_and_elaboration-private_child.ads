private package Initialization_And_Elaboration.Private_Child
  with Abstract_State => (State with Part_Of =>
                            Initialization_And_Elaboration.State)
is
   procedure Init (I : Integer)
     with Global => (Output => State);

   function Get return Integer
     with Global => State;
end Initialization_And_Elaboration.Private_Child;
