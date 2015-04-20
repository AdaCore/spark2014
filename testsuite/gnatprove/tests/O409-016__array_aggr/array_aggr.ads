package Array_Aggr with SPARK_Mode is
   procedure Bi_Dim_Aggr_OK (One : Natural) with
     Pre => One <= 1;
   procedure Bi_Dim_Aggr_KO (One : Natural);
end Array_Aggr;
