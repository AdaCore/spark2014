with P2; use P2;

package body Local_Variable_Pkg is

   function Func return Boolean is
      package Nested is
         V : T;
      end Nested;
   begin
      return True;
   end Func;

end Local_Variable_Pkg;
