with Assign_Arr; use Assign_Arr;
procedure Filter (X : in out Arr) is
   K : Integer := X'First;
begin
   for J in X'Range loop
      if X (J) > 0 then
	 X (K) := X (J);
	 K := K + 1;
      end if;
   end loop;
end Filter;
