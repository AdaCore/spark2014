with Assign_Arr; use Assign_Arr;
function Search_While (X : in Arr; Y : in Integer) return Integer is
   J : Integer := X'First;
begin
   while J <= X'Last loop
      if X (J) = Y then
         return J;
      end if;
      J := J + 1;
   end loop;
   return 0;
end Search_While;
