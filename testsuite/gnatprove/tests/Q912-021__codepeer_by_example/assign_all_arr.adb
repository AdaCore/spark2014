with Assign_Arr; use Assign_Arr;
procedure Assign_All_Arr (X : in out Arr) is
begin
   for J in X'Range loop
      X (J) := X (J) + 1;
   end loop;
end Assign_All_Arr;
