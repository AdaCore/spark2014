package body Array_Part_Of is
   protected body PO is

      procedure Init is
      begin
         for I in 1 .. 4 loop
            B (I) := 0;
         end loop;
      end Init;
   end PO;

end;
