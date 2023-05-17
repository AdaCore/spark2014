private package Refined_Global_Legal.Pr_Child
  with SPARK_Mode,
       Abstract_State => ((Pr_State  with Part_Of => State),
                          (Pr_State2 with Part_Of => State)),
       Initializes    => (Pr_State, Pr_State2)
is
   function Priv_F return Boolean
     with Global => Pr_State;
end Refined_Global_Legal.Pr_Child;
