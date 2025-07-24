with P;

procedure Main4 is -- @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (4);
begin
   P.Obj.PP1;
end Main4;
