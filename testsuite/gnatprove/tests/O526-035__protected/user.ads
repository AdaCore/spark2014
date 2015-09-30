pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
with Prot; use Prot;
package User
  with SPARK_Mode
is
   X : P;
   Y : Integer;

   procedure Proc;
end User;
