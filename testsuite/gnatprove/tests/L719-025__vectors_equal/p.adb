package body P is pragma SPARK_Mode (On);

   procedure Nearly_Identity_1 (L : in out Vector; I : Extended_Index) is
   begin
      Insert (L, I, 1);
      Delete (L, I);
   end Nearly_Identity_1;

   procedure Nearly_Identity_2 (L : in out Vector; I : Index_Type) is
      E : Element_Type := Element (L, I);
   begin
      Delete (L, I);
      Insert (L, I, E);
   end Nearly_Identity_2;

   procedure Identity_Swap (L : in out Vector; I1, I2 : Index_Type) is
      L_In : constant Vector := Copy (L);
   begin
      Swap (L, I1, I2);
      pragma Assert (Element (L, I1) = Element (L_In, I2));
      Swap (L, I1, I2);
   end Identity_Swap;

end P;
