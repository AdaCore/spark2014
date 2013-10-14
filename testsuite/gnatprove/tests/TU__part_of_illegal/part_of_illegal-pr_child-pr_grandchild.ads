private package Part_Of_Illegal.Pr_Child.Pr_Grandchild
  with SPARK_Mode,
       Abstract_State => (Grandchild_State with Part_Of => State)
is
   pragma Elaborate_Body (Part_Of_Illegal.Pr_Child.Pr_Grandchild);
end Part_Of_Illegal.Pr_Child.Pr_Grandchild;
