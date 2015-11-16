package body P
is

   protected body PO is
      procedure Dummy is
      begin
         X := not X;
      end;
   end;

end;
