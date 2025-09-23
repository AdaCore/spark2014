package body P is

   protected body PO1 is
      procedure PP11 is
      begin
         PA;
      end;
   end;

   procedure PA is
   begin
      PO2.PP21;
   end;

   protected body PO2 is
      procedure PP21 is
      begin
         PB;
      end;
   end;

   procedure PB is
   begin
      PO3.PP31;
   end;

   protected body PO3 is
      procedure PP31 is
      begin
         null;
      end;
   end;

end;
