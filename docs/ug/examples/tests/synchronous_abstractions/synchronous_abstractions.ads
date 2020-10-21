pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Synchronous_Abstractions with SPARK_Mode,
  Abstract_State => (Normal_State,
                     (Synchronous_State with Synchronous, External))
is
   procedure Do_Something with
     Global => (In_Out => Synchronous_State);
end Synchronous_Abstractions;
