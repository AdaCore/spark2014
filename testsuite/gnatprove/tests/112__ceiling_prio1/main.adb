with P;

procedure Main is  --  @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (10);
begin
   null;
end;
