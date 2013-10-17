private package Initializes_Illegal_5.Pr_Child
  with SPARK_Mode,
       Initializes => Pr_Var
is
   Pr_Var : Integer := 0
     with Part_Of => Initializes_Illegal_5.State;
end Initializes_Illegal_5.Pr_Child;
