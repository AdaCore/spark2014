pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P with SPARK_Mode is
   type Int_Acc is access Integer;

   protected type T is
      function F1 return Integer;
      procedure P1;
      procedure P2;
   private
      X : Int_Acc;
   end T;

end P;
