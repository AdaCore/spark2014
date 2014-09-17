pragma Warnings (Off, "subprogram * has no effect");
procedure Floats
is
   Dummy : constant Float := 1.0;
begin
   pragma Assert (False);  --  @ASSERT:FAIL
end Floats;
