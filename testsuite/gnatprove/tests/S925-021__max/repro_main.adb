pragma Warnings (Off, "is not referenced");
with Parent.Child;
pragma Warnings (On, "is not referenced");

procedure Repro_Main is
begin
   null;
end Repro_Main;
