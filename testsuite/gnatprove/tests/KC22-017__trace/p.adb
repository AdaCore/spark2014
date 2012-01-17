procedure P is
begin
   for B in Boolean'Range loop
      pragma Assert (B = not (not B));
      null;
   end loop;
end P;
