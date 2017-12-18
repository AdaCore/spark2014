package Part_Of is
   protected PO is
      procedure Proc;
      function Func return Integer;
   end PO;

   Var : Integer := 0 with Part_Of => PO;

   task TO;

   Part_Of_Task : Integer := 0 with Part_Of => TO;
end;
