package body Pack is pragma SPARK_Mode (On);

   procedure P2 is
   begin
      declare
         Z : Boolean := True;
      begin
         if True then
            return;
         end if;
      end;
   end;
end;
