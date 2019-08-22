package Invalid_Read_In_Elab_2 is
   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(34);
   Y : Int_Acc := X;

   package Nested with SPARK_Mode is
      Z : Integer := X.all;
   end Nested;
end Invalid_Read_In_Elab_2;
