package Pack is
   pragma SPARK_Mode (Off);

   type Tag is tagged null record;

   type Tag_Class_Ptr is access Tag'Class;

end Pack;
