package body P is
   protected body PT is
      entry E when G is
      begin
         null;
      end;
   end PT;

   task body T is
   begin
      loop
         RO1.C.E;
      end loop;
   end;
end;
