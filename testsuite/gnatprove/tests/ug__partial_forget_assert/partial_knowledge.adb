procedure Partial_Knowledge (X : Integer) is
   Y : Integer;
   Z : Integer;
begin
   Y := 0;
   if (X <= 0) then
      return;
   end if;
   begin
      Z := 1;
      begin
         if (X >= 2) then
            return;
         end if;
      end;
      pragma Assert_And_Cut (Y < Z);
      pragma Assert (Y = 0); -- Remembered
      pragma Assert (X > 0); -- Remembered
      pragma Assert (Y < Z); -- From cut
      pragma Assert (Z = 1); -- Forgotten
      pragma Assert (X < 2); -- Forgotten
   end;
end;
