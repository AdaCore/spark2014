package body P is

   package body Inner is
      protected body PO is
         procedure PP1 is
         begin
            null;
         end;
      end;

      procedure P1 is
      begin
         PO.PP1;
      end;

   begin
      --  Indirectly causes violation of the ceiling priority protocol when
      --  elaborated from a context with lower priority than PO.
      P1;
   end Inner;

end P;
