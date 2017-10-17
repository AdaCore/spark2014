with Assign_Arr; use Assign_Arr;
function Search (X : in Arr; Y : in Integer) return Integer is
begin
   for J in X'Range loop
      if X (J) = Y then
         return J;
      end if;
   end loop;
   return 0;
end Search;
