with P1; use P1;

package body Local_Variable_Subp is

   function Func return Boolean is
      V : T;
   begin
      return True;
   end Func;

end Local_Variable_Subp;
