with Gen;

procedure Main (Unused : Float) with Global => null is

   --  This subprogram provides a dummy context for instantiation of the
   --  generic unit. The dummy parameter prevents pulling the System into
   --  visibility graph, as it happens for main-like subprograms; the Global
   --  contract prevents "subprogram has no effect" warning.

   package Inst is new Gen;
begin
   null;
end;
