package Other2 is
   Visible_Var : Integer := 0;

   function Get_Private return Integer;

   function Get_Hidden return Integer;

private
   Priv_Var : Integer;
end Other2;
