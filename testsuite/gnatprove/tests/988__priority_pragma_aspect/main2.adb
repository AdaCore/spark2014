with P;

procedure Main2 with Priority => 4 is -- @CEILING_PRIORITY_PROTOCOL:FAIL
begin
   P.Obj.PP1;
end Main2;
