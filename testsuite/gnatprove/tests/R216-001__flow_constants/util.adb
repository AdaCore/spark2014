package body Util is
   protected body P is

      entry E_01 when Flag is
      begin
         Flag := Flag;
      end;

   end;

end Util;
