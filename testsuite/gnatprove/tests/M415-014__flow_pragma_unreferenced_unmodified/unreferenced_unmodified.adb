package body Unreferenced_Unmodified is
   function Return_5 (X, Y : Integer) return Integer is
      pragma Unreferenced (X, Y);
   begin
      return 5;
   end Return_5;

   procedure Do_Something (X, Y : in out Integer) is
      pragma Unmodified (X);
   begin
      if X + Y > 2 then
         Y := X;
      end if;
   end Do_Something;
end Unreferenced_Unmodified;
