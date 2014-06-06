procedure P (X : out Integer) is
   procedure Loc is
   begin
      X := 1;
   end Loc;
begin
   Loc;
   pragma Assert (X = 1);
end P;
