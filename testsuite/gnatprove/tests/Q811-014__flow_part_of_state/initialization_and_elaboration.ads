package Initialization_And_Elaboration
  with Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Get_It = 0
is
   procedure Init (I : in Integer)
     with Global => (Output => State);

   function Get_It return Integer
     with Global => State;
end Initialization_And_Elaboration;
