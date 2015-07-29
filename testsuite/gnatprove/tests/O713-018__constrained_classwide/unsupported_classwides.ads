package Unsupported_Classwides with SPARK_Mode is
   type Root (C : Natural) is tagged null record;
   type Root_01 is new Root (0) with null record;
   subtype Root_02 is Root (0);

   subtype CW_0 is Root'Class (0);

   RR : Root_01;
   R  : Root'Class := RR;
   R1 : Root_01'Class := RR;
   R2 : Root_02'Class := RR;
end Unsupported_Classwides;
