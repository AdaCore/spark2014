with Assign_Arr_Unk; use Assign_Arr_Unk;
procedure Bad_Assign_All_Arr_Unk (X : in out Arr) is
begin
   for J in X'Range loop
      X (J) := X (J + 1);
   end loop;
end Bad_Assign_All_Arr_Unk;
