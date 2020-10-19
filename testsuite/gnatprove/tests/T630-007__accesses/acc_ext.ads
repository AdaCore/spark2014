package Acc_Ext with SPARK_Mode is
   type Int_Acc is not null access Integer;
   P_Vol : Int_Acc := new Integer'(12) with Volatile;
end Acc_Ext;
