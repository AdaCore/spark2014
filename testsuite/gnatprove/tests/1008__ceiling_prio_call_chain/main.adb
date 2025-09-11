with P; use P;

procedure Main with Priority => 2 is -- @CEILING_PRIORITY_PROTOCOL:FAIL
begin
   null;
end Main;
