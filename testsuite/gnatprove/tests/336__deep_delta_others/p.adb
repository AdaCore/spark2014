procedure P (X : in out String) is
begin
   X := (@ with delta 1 => @ (1), 3 .. 4 => @ (@'Last), others => ' ');
end P;
