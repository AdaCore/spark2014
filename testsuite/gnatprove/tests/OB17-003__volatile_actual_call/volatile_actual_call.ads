package Volatile_Actual_Call is

   function Vol_Func return Boolean with Volatile_Function;

   protected PO is
      procedure Proc (X : Boolean);
      entry E (X : Boolean);
      function Func (X : Boolean) return Boolean;
   private
      B : Boolean := False;
   end;

   procedure Test;

end;
