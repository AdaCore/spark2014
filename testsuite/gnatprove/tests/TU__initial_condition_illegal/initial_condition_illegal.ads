package Initial_Condition_Illegal
  with SPARK_Mode
is
   package Incorrect_Placement
     --  TU: 1. An Initial_Condition aspect shall only be placed in an
     --  ``aspect_specification`` of a ``package_specification``.
     with Abstract_State => State,
          Initializes    => State
   is
      function F1 return Boolean
        with Global => State;
   end Incorrect_Placement;


   package Incorrect_Order_1
     --  TU: 2. The Initial_Condition aspect shall follow the Abstract_State
     --  aspect and Initializes aspect if they are present.
     with Abstract_State    => State,
          Initial_Condition => F1,
          Initializes       => State
   is
      function F1 return Boolean
        with Global => State;
   end Incorrect_Order_1;


   package Incorrect_Order_2
     --  TU: 2. The Initial_Condition aspect shall follow the Abstract_State
     --  aspect and Initializes aspect if they are present.
     with Initial_Condition => F1,
          Abstract_State    => State,
          Initializes       => State
   is
      function F1 return Boolean
        with Global => State;
   end Incorrect_Order_2;


   package Variable_Not_Denoted_By_Initializes
     --  TU: 7. Each variable or indirectly referenced state abstraction in an
     --  Initial_Condition aspect of a package Q which is declared immediately
     --  within the visible part of Q shall be initialized during the
     --  elaboration of Q and be denoted by a ``name`` of an
     --  ``initialization_item`` of the Initializes aspect of Q.
     with Initial_Condition => Var = 0
   is
      Var : Integer;
      procedure P1;
   end Variable_Not_Denoted_By_Initializes;
end Initial_Condition_Illegal;
