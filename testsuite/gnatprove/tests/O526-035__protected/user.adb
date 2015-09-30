pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package body User
  with SPARK_Mode
is
   procedure Proc is
   begin
      Y := X.Get * 2;  --  This call should be rejected
   end Proc;
end User;
