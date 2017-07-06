pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package body Prot with SPARK_Mode is

   protected body P is
      procedure Read is
      begin
         Count := Count + 1;
      end Read;
   end P;

end Prot;
