package Initial_Condition_Illegal_2
  --  TU: 7. Each variable or indirectly referenced state abstraction in an
  --  Initial_Condition aspect of a package Q which is declared immediately
  --  within the visible part of Q shall be initialized during the
  --  elaboration of Q and be denoted by a ``name`` of an
  --  ``initialization_item`` of the Initializes aspect of Q.
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => Var,
       Initial_Condition => F1 and Var = 0
is
   Var : Integer := 0;

   function F1 return Boolean
     with Global => State;
end Initial_Condition_Illegal_2;
