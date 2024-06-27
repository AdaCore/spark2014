pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P.Child with SPARK_Mode is

   protected type Prot is
      function Get return T;  --@INVARIANT_CHECK:FAIL
   private
      function Get_Priv return T;  --@INVARIANT_CHECK:NONE
   end Prot;

end P.Child;
