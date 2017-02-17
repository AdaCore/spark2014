with T;

package A
is

   pragma SPARK_Mode (On);

   procedure Get (
      X : in     T.Input_T;
      Y :    out T.Output_T);

end A;

