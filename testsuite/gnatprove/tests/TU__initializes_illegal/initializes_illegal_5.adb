with Initializes_Illegal_5.Pr_Child; pragma Elaborate_All (Initializes_Illegal_5.Pr_Child);

package body Initializes_Illegal_5
  with SPARK_Mode,
       Refined_State => (State => (Var,
                                   Initializes_Illegal_5.Pr_Child.Pr_Var))
is
   Var : Integer := Initializes_Illegal_5.Pr_Child.Pr_Var;

   function F1 return Integer
     with Refined_Global => Var
   is
   begin
      return Var;
   end F1;
end Initializes_Illegal_5;
