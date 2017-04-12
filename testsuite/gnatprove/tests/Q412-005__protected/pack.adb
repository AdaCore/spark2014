package body Pack is

   protected body PO_Func is

      function Func return Boolean is
      begin
         return True;
      end;

      entry E_Func when True is
         X : constant Boolean := Func;
      begin
         null;
      end;
   end;

end;
