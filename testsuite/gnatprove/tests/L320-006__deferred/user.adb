with Pack; use Pack;
procedure User (B : Boolean) is
begin
   if B then
      pragma Assert (X1.X = True);  -- must remain unprovable
      pragma Assert (X2 = 3);  -- should be unprovable
   else
      pragma Assert (Query_X1 = True);
      pragma Assert (Query_X2 = 3);
   end if;
end User;
