with Q;
with F;
procedure P is
begin
   Q;
   pragma Assert (F);  -- unprovable assertion
end P;
