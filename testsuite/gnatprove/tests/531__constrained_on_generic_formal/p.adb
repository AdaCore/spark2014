procedure P (X : in out T) is
begin
   pragma Assert (X'Constrained);
end;
