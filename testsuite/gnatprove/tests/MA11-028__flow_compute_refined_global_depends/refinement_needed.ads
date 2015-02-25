with Other; use Other;
pragma Elaborate_All (Other);

package Refinement_Needed
  with Abstract_State => (State, State2)
is
   V1, V2 : Integer := 0;

   function Foo return Integer
     with Global => (State);

   function Bar return Integer
     with Depends => (Bar'Result => (V1, V2, State2));

   function Hmmm return Integer
     with Global => Other_State;
end Refinement_Needed;
