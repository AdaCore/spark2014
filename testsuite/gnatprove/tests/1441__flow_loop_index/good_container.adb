with Iterable;

function Good_Container
  (A : Iterable.Container) return Integer
with Depends => (Good_Container'Result => A)
is
begin
   for E of A loop
      return E'Loop_Index.C;
   end loop;
   return 0;
end Good_Container;
