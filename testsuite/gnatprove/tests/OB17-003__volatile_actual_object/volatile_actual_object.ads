package Volatile_Actual_Object is

   Vol_Func : Boolean := True with Volatile;

   protected PO is
      procedure Proc (X : Boolean);
      entry E (X : Boolean);
      function Func (X : Boolean) return Boolean;
   private
      B : Boolean := False;
   end;

   task type TT (X : Boolean);

   TO : TT (Vol_Func);

   procedure Test;

end;
