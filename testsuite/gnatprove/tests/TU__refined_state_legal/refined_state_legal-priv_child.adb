package body Refined_State_Legal.Priv_Child
  with Refined_State => (Priv_State => Priv_Var)
is
   Priv_Var : Integer := 1;

   function F1 return Integer
     with Refined_Global => Priv_Var
   is
   begin
      return Priv_Var;
   end F1;
end Refined_State_Legal.Priv_Child;
