pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P with SPARK_Mode is
   type Int_Acc is access Integer;

   protected type T is
      function Get return Integer with Side_Effects;
      procedure Swap (Y : in out Int_Acc);
   private
      X : Int_Acc;
   end T;

   protected type T2 is
      function Get return Integer with Side_Effects;
      procedure Swap (Y : in out Int_Acc);
   private
      X : Int_Acc;
   end T2;

end P;
