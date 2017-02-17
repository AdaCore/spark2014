with T;

package Q
is

   pragma SPARK_Mode (On);

   procedure Convert (
                Raw_In : in     T.Input_T;
                Scale  : in     T.Scale_T;
                Value  :    out T.Output_T);

end Q;

