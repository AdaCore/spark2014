with P;
procedure Main is --@CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (2);
begin
   null;
end Main;
