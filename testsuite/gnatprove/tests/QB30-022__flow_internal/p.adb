package body P is

   protected body PO is

      procedure Proc is
         type T is record
            C : Integer := PO.X;
         end record;
      begin
         null;
      end;

   end PO;

   task body TO is

      type T is record
         C : Integer := X;
      end record;
   begin
      null;
   end;

end P;
