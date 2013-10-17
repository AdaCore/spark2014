package body Uninitialized is
   procedure Local (Y : out Integer) is
      X : Integer;
   begin
      if False then
         X := 0;
      end if;
      Y := X + 1;
   end Local;
end Uninitialized;
