package Lib with SPARK_Mode is
   type Big_Rec is record
      F : Integer := 1;
   end record;

   type Rec_Arr is array (1 .. 100) of Big_Rec;
   type Rec_Arr_Acc is access all Rec_Arr;

   Data_Ptr : constant Rec_Arr_Acc := new Rec_Arr;
end Lib;
