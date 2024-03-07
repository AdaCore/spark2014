with Gen;
with Inst;
procedure Main with SPARK_Mode is
   package Local is new Gen;
begin
   pragma Assert (Local.F = 0); --@ASSERT:PASS
   pragma Assert (Inst.F = 0); --@ASSERT:FAIL
end Main;
