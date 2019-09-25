with Repro;

procedure Repro_Main
is
   pragma Warnings (Off, "is not referenced");
   package Instance is new Repro (Integer, 8);
   pragma Warnings (On, "is not referenced");
begin
   null;
end Repro_Main;
