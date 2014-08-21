package Ineffective_Constant
  with Abstract_State => State,
       Initializes    => State
is
   procedure P
     with Global => State;
end Ineffective_Constant;
