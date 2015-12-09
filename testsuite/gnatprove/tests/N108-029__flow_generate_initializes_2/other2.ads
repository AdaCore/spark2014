package Other2
  with Abstract_State => State
is
   Visible_Var : Integer := 0;

   function Get_Private return Integer;

   function Get_Hidden return Integer;

private
   Priv_Var : Integer
     with Part_Of => state;
end Other2;
