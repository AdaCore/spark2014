package body Two_Tasks_Single_PO is

   protected body PO is
      entry E when True is
      begin
         null;
      end;
   end;

   task T1;
   task T2;

   task body T1 is
   begin
      PO.E;
   end;

   task body T2 is
   begin
      PO.E;
   end;

end;
