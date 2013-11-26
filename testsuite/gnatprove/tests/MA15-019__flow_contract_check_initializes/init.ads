package Init
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => (State, A)--  ,
       --  Initial_Condition => Sum_All = 0
is
   A : Integer := 0;

   function Sum_State return Integer
     with Global => State;

   function Sum_All return Integer
     with Global => (A, State);
private
   B : Integer := 0
     with Part_Of => State;
end Init;
