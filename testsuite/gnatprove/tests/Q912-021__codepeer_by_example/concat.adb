with Assign_Arr_Unk; use Assign_Arr_Unk;
procedure Concat (X, Y : in Arr; Z : out Arr) is
   K : Integer := 1;
begin
   for J in X'Range loop
      Z (K) := X (J);
      K := K + 1;
   end loop;
   for J in Y'Range loop
      Z (K) := Y (J);
      K := K + 1;
   end loop;
end Concat;
