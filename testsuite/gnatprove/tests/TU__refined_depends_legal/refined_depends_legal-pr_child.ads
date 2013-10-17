private package Refined_Depends_Legal.Pr_Child
  with SPARK_Mode,
       Abstract_State => (Pr_State with Part_Of => S3),
       Initializes    => (Pr_State, Pr_Var)
is
   Pr_Var : Integer := 10
     with Part_Of => S3;

   procedure Update_Pr_State
     with Global  => (Input  => Pr_Var,
                      In_Out => Pr_State),
          Depends => (Pr_State =>+ Pr_Var);
end Refined_Depends_Legal.Pr_Child;