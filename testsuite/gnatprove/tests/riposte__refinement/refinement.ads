package Refinement
  with Abstract_State => State,
       Initializes    => State
is
   type Reading is range -1 .. 100;

   function Get_Highest_Reading return Reading
     with Global => State;

   procedure Add_Reading (R : in Reading)
     with Global  => (In_Out => State),
          Depends => (State =>+ R),
          Pre     => R in 0 .. Reading'Last,
          Post    => Get_Highest_Reading > Reading'First;  --  @POSTCONDITION:PASS

end Refinement;
