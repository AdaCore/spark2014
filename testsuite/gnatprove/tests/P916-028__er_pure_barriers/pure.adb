package body Pure is

   protected body PT is
      entry E when N > 0 and B is
      begin
         pragma Assert (N > 0 and B);
      end E;
   end PT;

end;
