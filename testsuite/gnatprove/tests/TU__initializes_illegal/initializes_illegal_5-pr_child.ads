private package Initializes_Illegal_5.Pr_Child
  with Initializes => Pr_Var
is
   Pr_Var : Integer := 0
     with Part_Of => Initializes_Illegal_5.State;
end Initializes_Illegal_5.Pr_Child;
