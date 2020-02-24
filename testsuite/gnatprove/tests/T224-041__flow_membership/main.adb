with S;
with R;

procedure Main is
begin
   --  A demonstration that indeed both functions depend on their parameters
   pragma Assert (S (1, 2) /= S (1, 3));
   pragma Assert (R (1, 1) /= R (1, 2));
end;
