package body P with SPARK_Mode is

   protected body T is
      procedure Swap (Y : in out Int_Acc) is
         Tmp : Int_Acc := X;
      begin
         Y := Tmp;
         return;
      end Swap;
   end T;

end P;
