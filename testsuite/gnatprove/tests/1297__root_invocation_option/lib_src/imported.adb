package body Imported is
   procedure Check (X : Integer; Y : out Integer) is
   begin
      pragma Assert (X + 1 > X);
      Y := X + 1;
   end Check;
end Imported;
