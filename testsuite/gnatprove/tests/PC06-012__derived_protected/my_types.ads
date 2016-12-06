pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package My_Types with SPARK_Mode is
   protected type Prot is
      function Get_F return Integer;
      procedure Set_F (V : Integer) with
        Post => Get_F = V;
   private
      F : Integer := 0;
   end Prot;

   subtype Prot_2 is Prot;

   type Prot_3 is new Prot;

   type Prot_4 is new Prot_2;

   P_2 : Prot_2;
   P_3 : Prot_3;
   P_4 : Prot_4;

   procedure Use_P_2;

   procedure Use_P_3;

   procedure Use_P_4;
end My_Types;
