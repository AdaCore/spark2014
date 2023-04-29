procedure Proc (B : Boolean) with Global => null is
   S : String (1 .. 3);
   C : Boolean;
begin
   if B then
      null;
   else
      pragma Assert (C);
      raise Program_Error with S;
   end if;
exception
   when Program_Error =>
      null;
end;
