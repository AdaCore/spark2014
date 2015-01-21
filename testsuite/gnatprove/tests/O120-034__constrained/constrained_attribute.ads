package Constrained_Attribute with SPARK_Mode is
   type Mut_Rec (D : Integer := 0) is record
      F : Integer := 0;
   end record;

   function Is_Constrained (R : Mut_Rec) return Boolean is (R'Constrained) with
   Post => Is_Constrained'Result = R'Constrained;

   procedure Test;
end;
