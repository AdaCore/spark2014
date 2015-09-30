pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package body Prot
  with SPARK_Mode
is
   protected body P is
      procedure Add (X : Integer) is
      begin
         Val := Val + X;
      end Add;

      function Get return Integer is (Val);

      function Get_Double return Integer is (Get * 2);  --  This call should be accepted

   end P;

end Prot;
