pragma Spark_Mode;
package body Bug5 is
   function P (X : String) return Boolean
   is
   begin
      return True;
   end P;

   procedure Test is
   begin
      pragma Assert(P ("abcd"));
   end Test;
end Bug5;
