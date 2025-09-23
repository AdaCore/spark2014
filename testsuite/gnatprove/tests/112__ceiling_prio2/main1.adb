with U1;

procedure Main1 is -- @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (4);
begin
   U1.P1;
end Main1;
