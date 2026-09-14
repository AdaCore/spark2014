pragma Ada_2022;

procedure Bad_33 (S : String) with Global => null is
begin
   for E of S loop
      declare
         subtype S is Positive range 1 .. E'Loop_Index with Ghost;
         function F return Integer is (S'Last) with Ghost, Global => null;
      begin
         pragma Assert (F in S'Range);
      end;
   end loop;
end;
