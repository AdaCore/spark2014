package body Par.Priv2
  with Refined_State => (More_Private_State => E2)
is

   procedure Stuff
   is
   begin
      D2 := Par.Priv.D;
      --  par.priv|spec is visible
      --  par.priv|priv is not visible

   end Stuff;


end Par.Priv2;
