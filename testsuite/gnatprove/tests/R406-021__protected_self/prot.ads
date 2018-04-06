pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   protected type P (I : Integer) is
      procedure Add (X : Integer) with Pre => 2 * X < 10;
      function Get return Integer with Pre => 2 * I < 10;
   private
      Val : Integer := 0;
   end P;

end Prot;
