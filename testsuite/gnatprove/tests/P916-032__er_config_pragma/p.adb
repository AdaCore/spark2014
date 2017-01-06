package body P is
   protected body PT is
      entry E1 when False is
      begin
         null;
      end;

      entry E2 when False is
      begin
         null;
      end;

      entry E3 when False is
      begin
         null;
      end;
   end;

   task body T1 is
   begin
      loop
         PO.E1;
      end loop;
   end;

   task body T2 is
   begin
      loop
         PO.E2;
      end loop;
   end;

   task body T3 is
   begin
      loop
         PO.E3;
      end loop;
   end;

   task body T4 is
   begin
      loop
         PO.E1;
         PO.E2;
         PO.E3;
      end loop;
   end;
end;
