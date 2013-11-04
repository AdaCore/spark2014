with Par.Priv;

private package Par.Priv2
  with Abstract_State => (More_Private_State with Part_Of => State)
is

   D2 : Integer with Part_Of => State;

   procedure Stuff;

   function K return Integer is (Par.Priv.D);
   --  par.priv|spec is visible
   --  par.priv|priv is not visible


private

   E2 : Integer with Part_Of => More_Private_State;

   --  par.priv|spec is visible
   --  par.priv|priv is not visible

end Par.Priv2;
