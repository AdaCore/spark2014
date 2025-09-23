package body Prots is

   package body Gen is

      protected body PO is
         procedure PP1 is
         begin
            null;
         end;
      end;
   end;

   package PO1 is new Gen (1);
   package PO2 is new Gen (2);
   package PO3 is new Gen (3);

   procedure P1 is
   begin
      PO1.PO.PP1;
   end;

   procedure P2 is
   begin
      PO2.PO.PP1;
   end;

   procedure P3 is
   begin
      PO3.PO.PP1;
   end;

end Prots;
