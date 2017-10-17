with Assign_Arr_Unk; use Assign_Arr_Unk;
procedure Assign_All_Arr_Incr_Unk (X : in out Arr) is
begin
   for J in X'Range loop
      X (J) := X (J) + J;
   end loop;
end Assign_All_Arr_Incr_Unk;
