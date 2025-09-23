package body Prots is

   Data : Boolean := True;

   PO_Arr : array (1 .. 3) of PT;

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

   procedure Proc1 is
   begin
      null;
   end;
   procedure Proc2 is
   begin
      PO_Arr (2).PP2;
   end;
   procedure Proc3 is
   begin
      PO_Arr (3).PP1;
   end;

   procedure Flip is
   begin
      Data := not Data;
   end;

end Prots;
