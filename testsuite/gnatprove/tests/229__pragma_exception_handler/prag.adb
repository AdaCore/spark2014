procedure Prag (X : Boolean)
  with Global => null
is
begin
   if X then
      raise Program_Error;
   end if;
exception
   pragma Inspection_Point;
   when Program_Error =>
      null;
end;
