package body P is

   protected body PT is
      entry E1 when G is
      begin
         G := not G;
      end;

      entry E2 when not G is
      begin
         G := not G;
      end;
   end PT;

end P;
