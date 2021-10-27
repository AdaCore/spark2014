procedure Bad is
begin
   raise Program_Error;
   pragma Annotate (GNATprove, Intentional, "might be raised", "demo");
end;
