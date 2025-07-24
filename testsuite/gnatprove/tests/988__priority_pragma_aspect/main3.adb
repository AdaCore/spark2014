with P;

procedure Main3 is -- @CEILING_PRIORITY_PROTOCOL:PASS
   pragma Priority (2);
begin
   P.Obj.PP1;
end Main3;
