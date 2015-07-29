with Other2; use Other2;
pragma Elaborate_All (Other2);

package Generate_Initializes2
  with Abstract_State => State
is
   Visible : Integer := Visible_Var;  --  OK

   procedure Initialize_State;

private
   Priv : Integer
     with Part_Of => State;
end Generate_Initializes2;
