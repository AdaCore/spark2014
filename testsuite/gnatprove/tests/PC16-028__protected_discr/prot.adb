pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package body Prot
  with SPARK_Mode
is
   protected body P is
      procedure Add (X : Integer) is
      begin
         if B then
            Val := Val + X;
         end if;
      end Add;

      function Get return Integer is (Val);
   end P;

end Prot;
