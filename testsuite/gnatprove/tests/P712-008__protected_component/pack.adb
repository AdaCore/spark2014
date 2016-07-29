package body Pack is

   procedure Set (R : out Rec) is
   begin
      R.X := True;
   end Set;

   procedure Set (A : out Arr) is
   begin
      A := (others => True);
   end Set;

   protected body Prot is
      procedure P is
         Y : Boolean;
      begin
         Y := Get (X);
         Set (X);
         Set (A);
      end P;
   end Prot;

end Pack;
