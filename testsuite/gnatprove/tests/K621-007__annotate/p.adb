pragma SPARK_Mode (On);
package body P is
   G : Ptr;
   procedure Proc is
   begin
      G.all := 0;
   end;
end;
