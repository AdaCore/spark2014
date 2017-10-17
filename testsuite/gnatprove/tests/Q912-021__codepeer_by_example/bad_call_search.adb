with Assign_Arr; use Assign_Arr;
with Search;
function Bad_Call_Search return Integer is
   X : Arr;
begin
   for J in 1 .. 9 loop
      X (J) := J;
   end loop;
   return Search (X, 10);
end Bad_Call_Search;
