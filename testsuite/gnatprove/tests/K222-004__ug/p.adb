package body P is
   procedure Set is
   begin
      X.all := True;
   end Set;

   procedure P0 is
      Y : Boolean;

      function Get return Boolean is
         pragma Annotate (gnatprove, Ignore);
      begin
         return X.all;
      end Get;

      procedure P1 is
      begin
         if not Get then
            return;
         end if;
         Y := True;
      end P1;
   begin
      Set;
      P1;
   end P0;
end P;
