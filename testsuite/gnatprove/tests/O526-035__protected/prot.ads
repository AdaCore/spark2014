pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   protected type P is
      procedure Add (X : Integer);
      function Get return Integer;
      function Get_Double return Integer;
   private
      Val : Integer := 0;
   end P;

end Prot;
