with Reorder_P; use Reorder_P;
with Reorder_Q; use Reorder_Q;
with Unknown;
procedure Reorder_Main is
begin
   case Unknown.Value is
      when 0 =>
         pragma Assert (F1 = 1);
      when 1 =>
         pragma Assert (F2 = 1);
      when 2 =>
         pragma Assert (F3 = 1); -- unprovable
      when 3 =>
         pragma Assert (F4 = 1); -- unprovable
      when 4 =>
         pragma Assert (G1 = 1);
      when 5 =>
         pragma Assert (G2 = 1); -- unprovable
      when 6 =>
         pragma Assert (G3 = 1); -- unprovable
      when 7 =>
         pragma Assert (G4 = 1); -- unprovable
      when others =>
         null;
   end case;
end Reorder_Main;
