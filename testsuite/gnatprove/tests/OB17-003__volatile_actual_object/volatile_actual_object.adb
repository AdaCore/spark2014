package body Volatile_Actual_Object is

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

   task body TT is
      Y : Boolean := X;
   begin
      loop
         Y := not Y;
      end loop;
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
