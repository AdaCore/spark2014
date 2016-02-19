with Not_In_SPARK;

package Arr with SPARK_Mode is

   type Arr1 is array (Not_In_SPARK.Ind1,
                       Not_In_SPARK.Ind2,
                       Not_In_SPARK.Ind3) of Not_In_SPARK.T;

end;
