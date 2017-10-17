with Assign_Arr_Unk; use Assign_Arr_Unk;
function Search_Unk (X : in Arr; Y : in Integer) return Integer is
begin
   for J in X'Range loop
      if X (J) = Y then
         return J;
      end if;
   end loop;
   return 0;
end Search_Unk;
