package body Other2
  with Refined_State => (State => (Priv_Var, Hidden_Var))
is
   Hidden_Var : Integer;  --  not initialized

   function Get_Private return Integer is (Priv_Var);

   function Get_Hidden return Integer is (Hidden_Var);

begin
   Priv_Var := 10;
end Other2;
