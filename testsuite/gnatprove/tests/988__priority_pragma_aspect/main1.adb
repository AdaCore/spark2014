with P;

procedure Main1 with Priority => 2 is -- @CEILING_PRIORITY_PROTOCOL:PASS
begin
   P.Obj.PP1;
end Main1;
