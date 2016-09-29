pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package body Prot
  with SPARK_Mode
is
   protected body P is
      function Peek return Boolean is (G);
      procedure Flip is
         Tmp : constant Boolean := G;
      begin
         G := not Tmp;
      end Flip;
   end P;

end Prot;
