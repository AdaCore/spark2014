package body Bad_Ext_Ax with SPARK_Mode => Off is

   function Bad_Func (X : in out Integer) return Boolean is
   begin
      if X > Integer'Last / 2 then
         return False;
      end if;

      X := 2 * X;
      return True;
   end Bad_Func;

end;
