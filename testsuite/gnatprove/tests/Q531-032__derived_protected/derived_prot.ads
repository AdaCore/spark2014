pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Derived_Prot with SPARK_Mode is

   protected type Prot (C : Positive) is
      function Get_F return Natural with
        Post => Get_F'Result in 0 .. C;
      procedure Set_F (X : Natural) with
        Pre => X in 0 .. C;
   private
      F : Natural := 0;
   end Prot;

   type Prot2 is new Prot;
   type Prot3 is new Prot2;

end Derived_Prot;
