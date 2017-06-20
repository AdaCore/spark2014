package body Test is

   protected body PO is

      procedure Increment is
      begin
         if Count < Natural'Last then
            Count := Count + 1;
         end if;
      end Increment;

   end PO;

end Test;
