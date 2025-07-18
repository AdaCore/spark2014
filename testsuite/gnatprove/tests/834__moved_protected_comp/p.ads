pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P with SPARK_Mode is
   type Int_Acc is access Integer;

   protected type T is
      procedure Swap (Y : in out Int_Acc);
      -- Error, return from Swap with moved protected parameter
   private
      X : Int_Acc;
   end T;

end P;
