procedure Test_Enum with SPARK_Mode is
   type My_Enum is (One, Two, Three);
   for My_Enum use (5, 6, 7);

   type My_Enum_2 is (One_2, Two_2, Three_2);

   function Id (X : Integer) return Integer is (X);
   function Id (X : My_Enum) return My_Enum is (X);
   function Id (X : My_Enum_2) return My_Enum_2 is (X);
begin
   pragma Assert (My_Enum'Enum_Rep (Id (Two)) = 6);
   pragma Assert (My_Enum_2'Enum_Rep (Id (Two_2)) = 1);
   pragma Assert (My_Enum'Enum_Val (Id (6)) = Two);
   pragma Assert (My_Enum_2'Enum_Val (Id (1)) = Two_2);
end Test_Enum;
