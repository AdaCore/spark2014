package body P is

   protected body PO is
      procedure Dummy is
         type T is record
            C : Integer := PO'Size;
         end record;
         X : T;
      begin
         pragma Assert (X.C > 0);
      end;
   end;

end;
