with Gen;
-- We are "withing" a generic package whose body "withes" a package Q,
-- the elaboration of which calls a protected operation. We should detect
-- a failure of the check related to the ceiling priority protocol.
procedure Main is --@CEILING_PRIORITY_PROTOCOL:FAIL
   pragma Priority (3);
begin
   null;
end Main;
