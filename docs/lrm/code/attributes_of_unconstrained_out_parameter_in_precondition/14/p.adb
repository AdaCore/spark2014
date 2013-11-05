pragma SPARK_Mode (On);
package body P is

   procedure Init (X : out A) is
   begin
      X := (1 => X'Last, 20 => -1, others => 0);
   end Init;

end P;
