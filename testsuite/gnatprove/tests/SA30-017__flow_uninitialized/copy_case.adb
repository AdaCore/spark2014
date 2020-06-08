function Copy_Case (S : String) return String is

   Index : Positive := S'First;

   procedure Append (Y : in out String; C : Character) is
   begin
      Y (Index) := C;
      Index := Index + 1;
   end;

   Result : String (S'First .. S'Last);

begin
   for C of S loop
      case C is
         when ' ' => Append (Result, C);
         when 'A' => Append (Result, C);
         when others => Append (Result, C);
      end case;
   end loop;

   return Result;
end;
