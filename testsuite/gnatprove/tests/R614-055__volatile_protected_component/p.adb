package body P is
   protected body PT is
      function F return Boolean is
         Tmp : Integer := Integer (C);
      begin
         return Tmp = 0;
      end;
   end;
end;
