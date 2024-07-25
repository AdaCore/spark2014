pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package P2 with SPARK_Mode is
   type Int_Acc is access Integer;

   protected T is
      function F1 return Integer;
      procedure P1;
      procedure P2;
   private
   end T;

   X : Int_Acc with Part_Of => T;

end P2;
