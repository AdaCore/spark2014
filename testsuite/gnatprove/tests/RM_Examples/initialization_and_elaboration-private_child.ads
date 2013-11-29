private package Initialization_And_Elaboration.Private_Child
  with Abstract_State    => (State with Part_Of =>
                               Initialization_And_Elaboration.State),
       Initializes       => State,
       Initial_Condition => Get_Something = 0
is
   procedure Do_Something (I : in Integer)
     with Global => (In_Out => State);

   function Get_Something return Integer
     with Global => State;
end Initialization_And_Elaboration.Private_Child;
