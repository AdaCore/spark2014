package Volatiles_Illegal_13
  with SPARK_Mode
is
   type Vol_Int_T is new Integer with Volatile;

   type Record_T is record
      A : Integer;
      B : Vol_Int_T;
   end record;

   Error : Record_T;
end Volatiles_Illegal_13;
