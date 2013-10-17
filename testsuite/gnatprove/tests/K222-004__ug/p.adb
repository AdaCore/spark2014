package body P is
   pragma SPARK_Mode;
   procedure Set is
   begin
      X.all := True;
   end Set;

   procedure P0 is
      pragma SPARK_Mode (Off);

      Y : Boolean;

      function Get return Boolean is
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
