pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);
package Test_Access_Comp with SPARK_Mode is

   type R is record
      C : access Boolean;
   end record;

   protected P is
   private
      C : access Boolean;
   end P;

   type T is access Boolean;
   X : T;

   V : access Boolean := X with Part_Of => P;
end Test_Access_Comp;
