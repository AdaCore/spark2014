pragma SPARK_Mode (On);
with Parent_14.Private_Child_A_14,   -- OK
     Parent_14.Public_Child_A_14;    -- OK
package body Parent_14
is
   function F (X : Integer) return Integer is
   begin
      return Private_Child_A_14.F (X);
   end F;

   function G (X : Integer) return Integer is
   begin
      return Public_Child_A_14.G (X);
   end G;

end Parent_14;
