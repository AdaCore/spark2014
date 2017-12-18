package body Part_Of is

   protected body PO is
      procedure Proc is
         type T is record
            C : Integer := Var;
         end record;
      begin
         null;
      end Proc;

      function Func return Integer is
         type T is record
            C : Integer := Var;
         end record;
      begin
         return 0;
      end Func;

   end PO;

   task body TO is
      type T is record
         C : Integer := Part_Of_Task;
      end record;
   begin
      null;
   end;

end;
