with Assign_Arr; use Assign_Arr;
function Sum_All_Arr (X : in Arr) return Integer is
   Sum : Integer := 0;
begin
   for J in X'Range loop
      Sum := Sum + X (J);
   end loop;
   return Sum;
end Sum_All_Arr;
