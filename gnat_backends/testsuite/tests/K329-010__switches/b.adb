with A;
package body B is
   function F return Integer is
   begin
      return A.F;
   end F;
end B;
