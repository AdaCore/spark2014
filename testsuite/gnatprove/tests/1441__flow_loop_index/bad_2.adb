pragma Ada_2022;

procedure Bad_2 (A : String) with Global => null is
begin
   for E of A loop
      declare
         subtype S is Positive range 1 .. E'Loop_Index with Ghost;
         function F return Integer is (S'Last) with Ghost, Global => null;
      begin
         pragma Assert (F in A'Range);
      end;
   end loop;
end Bad_2;
