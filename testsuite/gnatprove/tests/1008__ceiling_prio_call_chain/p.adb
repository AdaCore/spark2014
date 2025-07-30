package body P is

   protected PO2
     with Priority => 1
   is
      procedure PP1
      with Global => null, Always_Terminates;
   end;

   protected body PO2 is
      procedure PP1 is
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

begin

   --  Indirectly causes violation of the ceiling priority protocol when
   --  elaborated from a context with lower priority than PO2.
   P1;

   --  Would indirectly cause the same violation again, but through a shorter
   --  call path. Disabled since we want to detect it already above.
   --  Q1;

   --  And here even more directly. Disabled as well.
   --  PO2.PP1;

end P;
