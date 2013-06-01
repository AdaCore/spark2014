procedure P is
begin
   for B in Boolean'Range loop
      pragma Loop_Invariant (B = not (not B));
      null;
   end loop;
end P;
