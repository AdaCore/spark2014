private package Initializes_Illegal_6.Pr_Child
  with SPARK_Mode,
       Initializes => Pr_Var
is
   Pr_Var : Integer := 0
     with Part_Of => Initializes_Illegal_6.State;
end Initializes_Illegal_6.Pr_Child;
