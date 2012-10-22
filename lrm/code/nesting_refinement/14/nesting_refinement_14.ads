package nesting_refinement_14
with
   Abstract_State => State,
   Initializes    => State
is
   procedure Operate_On_State
   with 
      Global  => In_Out => State;
end nesting_refinement_14;
