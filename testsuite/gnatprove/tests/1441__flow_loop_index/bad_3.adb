pragma Ada_2022;
with Iterable;

procedure Bad_3 (A : Iterable.Container) with Global => null is
begin
   for E of A loop
      declare
         subtype S is Positive range 1 .. Iterable.Cursor'(E'Loop_Index).C with Ghost;
         function F return Integer is (S'Last) with Ghost, Global => null;
      begin
         pragma Assert (F in A.Content'Range);
      end;
   end loop;
end Bad_3;
