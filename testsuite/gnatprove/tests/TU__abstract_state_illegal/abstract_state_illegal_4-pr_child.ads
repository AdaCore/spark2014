private package Abstract_State_Illegal_4.Pr_Child
  with SPARK_Mode,
       Abstract_State => (Pr_State with Part_Of => State)
is
   procedure Pr_P;
end Abstract_State_Illegal_4.Pr_Child;
