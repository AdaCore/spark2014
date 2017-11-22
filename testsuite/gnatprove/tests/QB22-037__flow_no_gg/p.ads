package P with Abstract_State => S, Initializes => S is
   function Get_Half return Integer with Global => S;
   --  Global contract references an abstract state, whose refinement is
   --  visible where the subprogram body is defined.
end;
