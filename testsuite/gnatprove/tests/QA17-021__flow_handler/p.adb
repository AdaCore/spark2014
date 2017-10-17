package body P is

   protected body PO1 is
      procedure Proc1 is
      begin
         X := not X;
      end;
   end;

   protected body PO2 is
      procedure Proc2 is
      begin
         X := not X;
      end;
   end;

end;
