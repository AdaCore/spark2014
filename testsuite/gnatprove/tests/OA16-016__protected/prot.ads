pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Prot
  with SPARK_Mode
is
   function Get return Boolean;

   protected P is
      function Peek return Boolean with
        Pre  => Get = True,
        Post => Peek'Result = True;
      procedure Flip;
   private
   end P;

private
   G : Boolean := False with Part_Of => P;
   function Get return Boolean is (G);
end Prot;
