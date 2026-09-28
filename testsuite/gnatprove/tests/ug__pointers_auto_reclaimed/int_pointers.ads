pragma Extensions_Allowed (On);

with SPARK.Pointers.Auto_Reclaimed.Global_Memory;

package Int_Pointers with SPARK_Mode is

   package Pointers is new
     SPARK.Pointers.Auto_Reclaimed.Global_Memory (Integer);

   function Id (X : Integer) return Integer is (X);

   procedure Create_Int is new Pointers.Create (Integer, Id);
   package Copy_Operations is new Pointers.Copy_Operations (Id);

end Int_Pointers;
