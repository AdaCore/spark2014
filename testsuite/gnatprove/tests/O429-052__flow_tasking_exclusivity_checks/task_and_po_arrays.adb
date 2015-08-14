package body Task_And_PO_Arrays is

   task body T is
   begin
      POs (Id).Dummy;
   end T;

   protected body PT is
      entry Dummy when True is
      begin
         null;
      end;
   end PT;

end;
