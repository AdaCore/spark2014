with Q;
package body P is
   pragma SPARK_Mode(On);

   procedure P (X : in out Integer) is
   begin
      Q.Tracing;
      X := X + 1;
   end P;

end P;
