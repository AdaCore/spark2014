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
end Initial_Condition_Illegal;
