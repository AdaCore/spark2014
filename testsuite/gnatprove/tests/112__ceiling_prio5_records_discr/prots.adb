package body Prots is

   protected body PT is
      procedure PP1 is
      begin
         null;
      end;
   end;

begin
   PO1.PP1;
   PO2.PP1;

   Obj1.F1.PP1;
   Obj1.F2.PP1;

   Obj2.F1.PP1;
   Obj2.F2.PP1;

end Prots;
