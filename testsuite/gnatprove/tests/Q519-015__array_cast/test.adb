Pragma SPARK_Mode(ON);

with cast_array; use cast_array;

procedure test is
   test_array : Int_array1 := (1, 2, 3);
   result_array : Int_array2;
begin
   result_array := Int_array2(test_array); --GNat OK, GNATProve error
   result_array := cast (test_array);  --GNAT OK, GNATPROVE OK
end test;
