with Pack;

procedure Main2 with Pre => Pack.I < 6 is --@PRECONDITION_MAIN:FAIL
begin
   pragma Assert (Pack.I = 5); --@ASSERT:FAIL
end Main2;
