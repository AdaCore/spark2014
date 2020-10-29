package body P is
   protected body PT is
      entry E (Callback : not null access procedure) when True is
      begin
         Callback.all;
      end;
   end;
end;
