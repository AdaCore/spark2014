function Func (B : Boolean) return Boolean is
   C : Boolean;
   S : String (1 .. 3);
begin
   return (if B then True else C and raise Program_Error with S);
exception
   when Program_Error =>
      return False;
end;
