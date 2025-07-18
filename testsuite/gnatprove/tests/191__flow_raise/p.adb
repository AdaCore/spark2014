procedure P with Global => null is
   B, C : Boolean;
   S1 : String (1 .. 3);
   S2 : String (1 .. 3);

   function Func1 return Boolean is
   begin
      return (if B then True else C and raise Program_Error with S1);
   end;

   function Func2 return Boolean is
   begin
      if B then
         return True;
      else
         pragma Assert (C);
         raise Program_Error with S2;
      end if;
   end;

begin
   pragma Assert (Func1);
   pragma Assert (Func2);
end;
