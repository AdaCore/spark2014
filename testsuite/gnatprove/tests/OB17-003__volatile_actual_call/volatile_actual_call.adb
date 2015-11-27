package body Volatile_Actual_Call is

   function Vol_Func return Boolean is (True);

   protected body PO is
      procedure Proc (X : Boolean) is
      begin
         B := X;
      end;

      entry E (X : Boolean) when True is
      begin
         B := X;
      end;

      function Func (X : Boolean) return Boolean is (B = X);

   end;

   procedure Test is
      Dummy : constant Boolean := PO.Func (Vol_Func);
   begin
      if Dummy then
         PO.Proc (Vol_Func);
      else
         PO.E (Vol_Func);
      end if;
   end;

end;
