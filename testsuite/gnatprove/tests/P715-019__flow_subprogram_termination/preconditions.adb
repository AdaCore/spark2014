package body Preconditions is

   function Nonreturning_Precondition (A, B : Integer) return Boolean is
      Result : Boolean := False;
   begin
      while True loop
         Result := (A = B);
      end loop;
      return Result;
   end;
end;
