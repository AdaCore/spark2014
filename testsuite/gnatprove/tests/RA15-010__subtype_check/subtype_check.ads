package Subtype_Check with SPARK_Mode is
   function Id (X : Integer) return Integer is (X);

   Zero : constant Integer := Id (0);

   subtype My_Natural is Integer range Zero .. 100;

   type R (D : My_Natural) is null record;

   type R_Acc is access R;

   X : R_Acc := new R (-1); --@RANGE_CHECK:FAIL
end Subtype_Check;
