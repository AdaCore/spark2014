package body P is

   protected body PO1 is
      procedure PP11 is
      begin
         null;
      end;
   end;

   procedure P2B is
   begin
      PO2.PP21;
   end;

   procedure P2 is
   begin
      P2B;
   end;

   protected body PO2 is
      procedure PP21 is
      begin
         P3;
      end;
   end;

   procedure P3B is
   begin
      PO3.PP31;
   end;

   procedure P3 is
   begin
      P3B;
   end;
   protected body PO3 is
      procedure PP31 is
      begin
         P4;
      end;
   end;

   procedure P4B is
   begin
      PO4.PP41;
   end;

   procedure P4 is
   begin
      P4B;
   end;
   protected body PO4 is
      procedure PP41 is
      begin
         null;
      end;
   end;

begin
   P.PO1.PP11;
   P.P2;
end;
