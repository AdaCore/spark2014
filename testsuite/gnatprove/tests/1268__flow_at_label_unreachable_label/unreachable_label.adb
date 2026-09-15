pragma Extensions_Allowed (All_Extensions);

procedure Unreachable_Label is
   X : Boolean := False;
begin
   if False then
      <<L>>
      X := not X;
      X := X'At (L);
      declare
         Y : Boolean := False;
      begin
         Y := not Y;
      end;
   end if;
end Unreachable_Label;
