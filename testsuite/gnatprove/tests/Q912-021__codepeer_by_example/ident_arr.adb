procedure Ident_Arr (X : out Arr) is
begin
   for J in X'Range loop
      X (J) := J;
   end loop;
end Ident_Arr;
