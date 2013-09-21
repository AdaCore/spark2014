package Reduced_02
  with SPARK_Mode
is

   type F32 is new Float;
   type F64 is new Long_Float;

   function Double_To_Single (X : F64) return F32
     is (F32 (X))
     with Pre =>
       (X >= F64 (F32'First) and then
        X <= F64 (F32'Last));


end Reduced_02;
