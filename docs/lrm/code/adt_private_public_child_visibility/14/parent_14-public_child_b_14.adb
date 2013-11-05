pragma SPARK_Mode (On);
with Parent_14.Private_Child_B_14;
package body Parent_14.Public_Child_B_14
is
   function H (X : Integer) return Integer is
   begin
      return Parent_14.Private_Child_B_14.H (X);
   end H;
end Parent_14.Public_Child_B_14;
