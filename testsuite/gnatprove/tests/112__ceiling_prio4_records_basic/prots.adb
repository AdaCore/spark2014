package body Prots is

   Obj : R;

   protected body PT1 is
      procedure PP1 is
      begin
         null;
      end;
   end;

   protected body PT2 is
      procedure PP2 is
      begin
         null;
      end;
   end;

   protected body PO is
      procedure PP0 is
      begin
         null;
      end;
   end;

   procedure Proc1 is
   begin
      Obj.F1.PP1; -- Ceiling priority of the callee is 3
      PO.PP0;     -- Ceiling priority of the callee is 3
   end;

   procedure Proc2 is
   begin
      Obj.F2.PP2; -- Ceiling priority of the callee is 4
      Obj.F3.PP1; -- Ceiling priority of the callee is 3
   end;

end Prots;
