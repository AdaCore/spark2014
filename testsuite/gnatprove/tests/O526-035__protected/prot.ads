pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   protected type P is
      procedure Add (X : Integer);
      function Get return Integer;
      function Get_Vol return Integer with Volatile_Function;
      function Get_Double return Integer;
      function Get_Vol_Double return Integer with Volatile_Function;
   private
      Val : Integer := 0;
   end P;

end Prot;
