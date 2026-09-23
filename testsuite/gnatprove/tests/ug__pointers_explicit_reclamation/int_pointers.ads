with SPARK.Pointers.Explicit_Reclamation.Global_Memory;

package Int_Pointers with SPARK_Mode is

   function Is_Reclaimed (Unused : Integer) return Boolean is (True)
   with Ghost => Static;

   package Pointers is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (Integer, Is_Reclaimed);

   function Id (X : Integer) return Integer is (X);

   procedure Create_Int is new Pointers.Create (Integer, Id);
   package Copy_Operations is new Pointers.Copy_Operations (Id);

end Int_Pointers;
