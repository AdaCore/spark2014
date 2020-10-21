with Ada.Strings.Maps; use Ada.Strings.Maps;

procedure Test is
   A : Character_Sequence := "abcd";
   B : Character_Sequence := "zzzz";
   Map : Character_Mapping := To_Mapping (A, B);
begin
   for Char of A loop
      pragma Assert (Value (Map, Char) /= Char);
   end loop;
end Test;
