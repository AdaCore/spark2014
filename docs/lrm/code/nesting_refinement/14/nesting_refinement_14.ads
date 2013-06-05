package Nesting_Refinement_14
   with Abstract_State => State,
        Initializes    => State
is
   procedure Operate_On_State
      with Global  => (In_Out => State);
end Nesting_Refinement_14;
