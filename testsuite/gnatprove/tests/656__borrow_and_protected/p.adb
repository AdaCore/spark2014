pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package body P with SPARK_Mode is

   protected body T is
      function F1 return Integer is (42);
      function F2 return Integer is (X.all);

      procedure Q with Pre => True is
      begin
         if X /= null then
            X.all := X.all + 1;
         end if;
      end Q;

      procedure P1 is
         Tmp : Int_Acc := X;
      begin
	 null;
      end P1;

      procedure P2 is
         Tmp : Int_Acc := X;
      begin
         Q;
         X := Tmp;
      end P2;

      procedure P3 is
         Tmp : Int_Acc := X;
	 Y : Integer;
      begin
         Y := F1;
         Y := F2;
      end P3;

      procedure IP1 is
         Tmp : Int_Acc := X;
      begin
	 null;
      end IP1;

      procedure IP2 is
         Tmp : Int_Acc := X;
      begin
         Q;
         X := Tmp;
      end IP2;

      procedure IP3 is
         Tmp : Int_Acc := X;
	 Y : Integer;
      begin
         Y := F1;
         Y := F2;
      end IP3;

   end T;

end P;
