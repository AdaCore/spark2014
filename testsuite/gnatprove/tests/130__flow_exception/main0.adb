procedure Main0 (X : Boolean; Y : out Boolean)
  with Global => null, Post => Y = X
is
begin
   if X then
      raise Constraint_Error;
   else
      raise Program_Error;
   end if;
exception
   when Constraint_Error =>
      Y := True;
   when Program_Error =>
      Y := False;
end;
