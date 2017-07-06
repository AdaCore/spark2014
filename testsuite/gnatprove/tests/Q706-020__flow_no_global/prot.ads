pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Prot with SPARK_Mode is

   protected P is
      procedure Read;
   private
      Count : Integer := 0;
   end P;

end Prot;
