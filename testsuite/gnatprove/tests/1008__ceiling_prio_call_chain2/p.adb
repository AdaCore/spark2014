package body P is

   protected body PT is
      procedure PP1 is
      begin
         null;
      end;
      procedure PP2 is
      begin
         null;
      end;
   end;

   procedure Q2 is
   begin
      PO2.PP1;
   end;

   procedure Q1 is
   begin
      Q2;
   end;

   procedure P1 is
   begin
      Q1;
   end;

   function F return Integer with Side_Effects is
   begin
      PO1.PP1;
      PO1.PP2;
      PO2.PP2;
      return 1;
   end;

   X : Integer;

begin

   --  Indirectly causes violation of the ceiling priority protocol when
   --  elaborated from a context with lower priority than PO2.
   X := F;

   --  Same here.
   P1;

--  Would indirectly cause the same violation again, but through a shorter
--  call path. Disabled since we want to detect it already above.
--  Q1;

--  And here even more directly. Disabled as well.
--  PO2.PP1;

end P;
