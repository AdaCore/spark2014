procedure Main_Case (Y : out Integer) is
   X : Integer;
begin
   case X is
      when 1 =>
         Y := X;
      when others =>
         Y := 0;
   end case;
end Main_Case;
