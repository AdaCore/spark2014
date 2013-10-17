with Refined_State_Legal.Priv_Child;

package body Refined_State_Legal
  with Refined_State => (S1 => (Var1,
                                Refined_State_Legal.Priv_Child.Priv_State),
                         S2 => Var2)
is
   Var1, Var2 : Integer;

   procedure Do_Nothing is begin null; end;
end Refined_State_Legal;