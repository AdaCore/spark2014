with Assign_Arr; use Assign_Arr;
procedure Assign_All_Arr_Incr (X : in out Arr) is
begin
   for J in X'Range loop
      X (J) := X (J) + J;
   end loop;
end Assign_All_Arr_Incr;
