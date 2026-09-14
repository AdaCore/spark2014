pragma Ada_2022;
with Iterable;

procedure Bad_4 (A : Iterable.Container) with Global => null is
begin
   for E of A loop
      pragma Assert (Iterable.Cursor'(E'Loop_Index).C in A.Content'Range);
   end loop;
end Bad_4;
