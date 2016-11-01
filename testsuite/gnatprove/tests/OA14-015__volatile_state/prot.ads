pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   protected P is
      function Peek return Boolean;
      procedure Flip;
   private
   end P;

private
   G : Boolean := False with Part_Of => P;
end Prot;
