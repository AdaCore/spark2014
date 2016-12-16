pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   protected type P (B : Boolean) is
      procedure Add (X : Integer);
      function Get return Integer;
   private
      Val : Integer := 0;
   end P;

end Prot;
