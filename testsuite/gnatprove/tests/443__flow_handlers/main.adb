with Handlers;
with Pkg;

procedure Main is
   use type Handlers.No_Param_Proc;
begin
   --  We expect check when processing the withed unit, but not here
   pragma Assert (Pkg.P_Local /= null);
end;
