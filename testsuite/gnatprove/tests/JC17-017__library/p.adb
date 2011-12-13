function P (X : Integer) return Integer is
begin
   pragma Assert (X + X >= 0);
   return X;
end;
