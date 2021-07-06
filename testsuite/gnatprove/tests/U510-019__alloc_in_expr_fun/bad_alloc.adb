procedure Bad_Alloc with SPARK_Mode is
   type My_Int is new Integer with Default_Value => 0;
   type My_Int_Acc is access My_Int;

   function New_My_Int return My_Int_Acc is (new My_Int);

   X : My_Int_Acc := New_My_Int;
begin
   pragma Assert (X.all = 0);
end Bad_Alloc;
