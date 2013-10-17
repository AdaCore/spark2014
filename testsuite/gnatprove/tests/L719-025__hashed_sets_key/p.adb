package body P is  pragma SPARK_Mode (On);

   procedure Identity (L : in out Set; K : Key_Type) is
      E : Element_Type := Element (L, K);
   begin
      Replace (L, K, E);
   end Identity;

end P;
