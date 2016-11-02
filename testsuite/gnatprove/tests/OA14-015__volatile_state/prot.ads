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

   function Get return Boolean with Global => P, Volatile_Function;

private
   G : Boolean := False with Part_Of => P;

   function Get return Boolean is (P.Peek);
end Prot;
