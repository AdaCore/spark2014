with Refined_Global_Legal.Pr_Child;

package body Refined_Global_Legal
  with Refined_State => (State  => (Refined_Global_Legal.Pr_Child.Pr_State,
                                    Refined_Global_Legal.Pr_Child.Pr_State2),
                         State2 => (Var, Var2),
                         State3 => (Var3, Var4))
is
   Var, Var2, Var3, Var4 : Integer := 1;


   procedure P1
     with Refined_Global => (Input  => Refined_Global_Legal.Pr_Child.Pr_State,
                             Output => (Var, Var2, Var3),
                             In_Out => Var4)
   is
   begin
      if Refined_Global_Legal.Pr_Child.Priv_F then
         Var  := 1 + Var4;
         Var2 := 2 + Var4;
         Var3 := 3 + Var4;
         Var4 := 4 + Var4;
      else
         Var  := 1 - Var4;
         Var2 := 2 - Var4;
         Var3 := 3 - Var4;
         Var4 := 4 - Var4;
      end if;
   end P1;
end Refined_Global_Legal;
