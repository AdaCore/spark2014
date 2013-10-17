limited with Part_Of_Illegal.Pr_Child.Pr_Grandchild;

private package Part_Of_Illegal.Pr_Child
  with SPARK_Mode
is
   Pr_Child_Vis_1 : Integer --  Grandchild is less visible
     --  TU: 3. A variable or state abstraction which is part of the visible
     --  state of a private child unit (or a public descendant thereof) shall
     --  have its Part_Of indicator specified; the Part_Of indicator shall
     --  denote a state abstraction declared by either the parent unit of the
     --  private unit or by a public descendant of that parent unit.
     with Part_Of => Part_Of_Illegal.Pr_Child.Pr_Grandchild.Grandchild_State;


   Pr_Child_Vis_2 : Integer;  --  Visible state is not connected
   --  TU: 3. A variable or state abstraction which is part of the visible
   --  state of a private child unit (or a public descendant thereof) shall
   --  have its Part_Of indicator specified; the Part_Of indicator shall
   --  denote a state abstraction declared by either the parent unit of the
   --  private unit or by a public descendant of that parent unit.
end Part_Of_Illegal.Pr_Child;
