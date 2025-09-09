with U1;

procedure Main2 is -- @CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (4);
begin
   U1.PAA;
end Main2;
