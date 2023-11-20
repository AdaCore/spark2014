package Volatiles_Illegal_10
  with SPARK_Mode
is
   type Vol_Scalar_T is mod 2**32 with Volatile;

   procedure Scalar_Formal_Parameter (Par : in out Vol_Scalar_T);
end Volatiles_Illegal_10;
