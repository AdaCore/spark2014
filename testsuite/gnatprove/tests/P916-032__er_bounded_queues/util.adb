package body Util is
   protected body P is

      entry E_01 when Flag is
      begin
         Flag := Flag;
      end;

      entry E_02 when True is
      begin
         null;
      end;

      entry E_03 when False is
      begin
         null;
      end;

   end;

   task body T_01 is
   begin
      loop
         PO.E_01;
      end loop;
   end;

   task body T_02 is
   begin
      loop
         PO.E_02;
      end loop;
   end;

   task body T_03 is
   begin
      loop
         PO.E_03;
      end loop;
   end;

end Util;
