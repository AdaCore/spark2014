package body Pack is

   protected body Store is

      procedure Dummy is
      begin
         null;
         --  Crash happens only with a delay statement here
         delay 0.0;
      end Dummy;
   end Store;

end Pack;
