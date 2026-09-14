pragma Ada_2022;

procedure Bad_1 (A : String) is
begin
   for E of A loop
      declare
         function F return Integer is (E'Loop_Index) with Ghost, Global => null;
      begin
         pragma Assert (F in A'Range);
      end;
   end loop;
end Bad_1;
