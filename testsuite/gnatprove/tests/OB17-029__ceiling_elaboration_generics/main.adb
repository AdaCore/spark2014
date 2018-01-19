with Gen;
-- We are "withing" a generic package whose body "withes" a package Q,
-- the elaboration of which calls a protected operation. We should detect
-- a failure of the check related to the ceiling priority protocol
-- but we don't.
procedure Main is
   pragma Priority (3);
begin
   null;
end Main;
