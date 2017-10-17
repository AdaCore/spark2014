with Assign_Arr; use Assign_Arr;
function Search_Loop (X : in Arr; Y : in Integer) return Integer is
   J : Integer := X'First;
begin
   loop
      if J > X'Last then
         return 0;
      end if;
      if X (J) = Y then
         return J;
      end if;
      J := J + 1;
   end loop;
end Search_Loop;
