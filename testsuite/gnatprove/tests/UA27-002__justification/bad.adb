procedure Bad is
   pragma Annotate (GNATprove, Intentional, "raise exceptions", "demo");
begin
   raise Program_Error;
   pragma Annotate (GNATprove, Intentional, "might be raised", "demo");
end;
