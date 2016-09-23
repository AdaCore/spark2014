package body Util is

   function Exclusive_Or (A, B : Boolean) return Boolean
   is
   begin
      return A xor B;
   end Exclusive_Or;

end Util;
