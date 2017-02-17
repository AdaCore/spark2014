package body Unreferenced_Unmodified is
   type Record_T is record
      X, Y : Integer;
   end record;

   function Return_5 (X, Y : Integer ; Rec : Record_T) return Integer is
      pragma Unreferenced (X, Y);
      pragma Unreferenced (Rec);
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
