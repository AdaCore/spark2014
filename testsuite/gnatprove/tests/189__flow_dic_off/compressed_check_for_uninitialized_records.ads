package Compressed_Check_For_Uninitialized_Records with SPARK_Mode is

   type Rec is record
      A : Natural;
      B : Natural;
   end record;

   R : Rec;

   procedure Initialize;

   procedure Use_Rec;

end Compressed_Check_For_Uninitialized_Records;
