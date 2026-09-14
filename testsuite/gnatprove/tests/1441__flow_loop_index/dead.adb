pragma Ada_2022;
with Iterable;

function Dead (A : Iterable.Container) return Integer
  with Depends => (Dead'Result => A), Ghost
is
begin
   if False then
      for E of A loop
         return E'Loop_Index.C;  -- do not warn about 'Loop_Index in dead code
      end loop;
   end if;

   return A.Max;
end;
