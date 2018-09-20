with Pack;

procedure Main with Pre => Pack.I < 10 is --@PRECONDITION_MAIN:PASS
begin
   pragma Assert (Pack.I = 5); --@ASSERT:FAIL
end Main;
