function Copy_If (S : String) return String is

   Index : Positive := S'First;

   procedure Append (Y : in out String; C : Character) is
   begin
      Y (Index) := C;
      Index := Index + 1;
   end;

   Result : String (S'First .. S'Last);

begin
   for C of S loop
      if C = ' ' then
         Append (Result, C);
         elsif C = 'A' then Append (Result, C);
         else Append (Result, C);
      end if;
   end loop;

   return Result;
end;
