pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Procedure_On_Protected with SPARK_Mode is
   type R is record
      F : Integer;
   end record;

   procedure Init (X : out R);

   protected Obj is
      procedure Do_Init;
   private
      C : R := (F => 1);
   end Obj;

end Procedure_On_Protected;
