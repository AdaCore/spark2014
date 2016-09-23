package Util with Elaborate_Body is

   function Exclusive_Or (A, B : Boolean) return Boolean
   with Post => (if A
                 then Exclusive_Or'Result = not B
                 else Exclusive_Or'Result = B);

end Util;
