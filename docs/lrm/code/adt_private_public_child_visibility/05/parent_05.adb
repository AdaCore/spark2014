with Parent_05.Private_Child_A_05,   -- OK
     Parent_05.Public_Child_A_05;    -- error, public children not visible
package body Parent_05
is
   function F (X : Integer) return Integer is
   begin
      return Private_Child_A_05.F (X);
   end F;

   function G (X : Integer) return Integer is
   begin
      return Public_Child_A_05.G (X);
   end G;

end Parent_05;
