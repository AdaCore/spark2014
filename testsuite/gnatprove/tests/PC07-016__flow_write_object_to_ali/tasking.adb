package body tasking is
   protected body PT is
      entry E when G is
      begin
         null;
      end;
   end PT;

   task body T1 is
   begin
      loop
         RO1.C1.E;
      end loop;
   end;

   task body T2 is
   begin
      loop
         RO1.C2.E;
      end loop;
   end;
end;
