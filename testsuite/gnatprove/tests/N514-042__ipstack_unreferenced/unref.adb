procedure Unref (Y : out Integer) is
   X : Integer;
   pragma Unreferenced (X);
   procedure Set (X, Y : out Integer) with
     Global => null
   is
   begin
      X := 10;
      Y := 10;
   end Set;
begin
   Set (X, Y);
end Unref;
