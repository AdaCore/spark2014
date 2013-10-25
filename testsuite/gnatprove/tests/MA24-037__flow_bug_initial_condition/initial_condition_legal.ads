package Initial_Condition_Legal
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => F1
is
   function F1 return Boolean
     with Global => State;
end Initial_Condition_Legal;
