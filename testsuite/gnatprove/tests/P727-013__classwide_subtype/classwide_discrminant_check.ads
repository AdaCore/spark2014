package Classwide_Discrminant_Check with SPARK_Mode is
   type Root (D : Natural) is tagged record
      F : Integer := 0;
   end record;

   subtype Root_Class is Root'Class;

   function Get_F (A : Root_Class) return Integer is (A.F);
end Classwide_Discrminant_Check;
