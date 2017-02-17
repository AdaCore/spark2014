with T;
package body P is pragma SPARK_Mode (On);
   procedure Proc is
   begin
      T.X := T.X + 1;
   end Proc;
end P;
