package body P is

   protected body PO is
      procedure Dummy (Arg : Integer) is
         procedure Inner is
         begin
            pragma Assert (Arg = 0);
         end;
      begin
         Inner;
      end;
   end;

   task body TT is
   begin
      loop
         PO.Dummy (0);
      end loop;
   end;
end;
