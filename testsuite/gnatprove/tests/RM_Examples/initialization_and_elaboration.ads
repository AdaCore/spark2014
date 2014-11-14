with P;
pragma Elaborate_All (P);  --  required because P.VP is used in initialization of V

package Initialization_And_Elaboration
  with Abstract_State    => State,
       Initializes       => (State,
                             V => P.VP),  -- Initializing V depends on P.VP
       Initial_Condition => V = P.VP and Get_It = 0
is
   V : Integer := P.VP;

   procedure Do_It (I : in Integer)
     with Global => (In_Out => State);

   function Get_It return Integer
     with Global => State;
end Initialization_And_Elaboration;
