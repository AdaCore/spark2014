with Parent;

procedure Init (Unused : Boolean) is
   pragma Unreferenced (Unused);
   --  Without this extra parameter GNATprove would think that proxy is a
   --  main-like function and check initialization of its global inputs and
   --  proof_ins, which we only want to be checked for Main.
begin
   Parent.Init;
end;
