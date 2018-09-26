package P_Warn with SPARK_Mode is
   type My_Enum is (A, B, C);

   X1 : My_Enum := A;

   pragma Assert (X1'Img'First = 1);
   pragma Assert (My_Enum'Image (X1)'Length <= 255 * 8);

   X2 : Integer := 1;

   pragma Assert (X2'Img'First = 1);
   pragma Assert (Integer'Image (X2)'Length <= 21);

   X3 : Long_Long_Integer := 1;

   pragma Assert (X3'Img'First = 1);
   pragma Assert (Long_Long_Integer'Image (X3)'Length <= 21);

   X4 : Short_Short_Integer := 1;

   pragma Assert (X4'Img'First = 1);
   pragma Assert (Short_Short_Integer'Image (X4)'Length <= 5);
   pragma Assert (Short_Short_Integer'Image (X4)'Length = 2);
end P_Warn;
