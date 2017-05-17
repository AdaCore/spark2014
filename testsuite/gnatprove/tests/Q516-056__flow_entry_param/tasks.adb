package body Tasks is

   protected body Store is
      entry Wait (Dummy : Integer) when True is
      begin
         null;
      end;
   end;

end;
