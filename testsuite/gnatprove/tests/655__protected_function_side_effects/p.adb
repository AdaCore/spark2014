package body P with SPARK_Mode is
   procedure P (X : not null Int_Acc) is
   begin
      X.all := 1;
   end P;

   protected body T is
      function Get return Integer is
      begin
         if X /= null then
            P (X); --  Get should not be allowed to modify X
            return X.all;
         end if;
         return 0;
      end Get;
      procedure Swap (Y : in out Int_Acc) is
         Tmp : Int_Acc := X;
      begin
         X := Y;
         Y := Tmp;
      end Swap;
   end T;

   protected body T2 is
      function Internal return Integer with Side_Effects;
      function Internal return Integer is
      begin
         if X /= null then
            P (X); --  Internal should not be allowed to modify X
            return X.all;
         end if;
         return 0;
      end Internal;
      function Get return Integer is
         X : Integer;
      begin
         X := Internal; --  Calling Internal is fine as it cannot modify X
         return X;
      end Get;
      procedure Swap (Y : in out Int_Acc) is
         Tmp : Int_Acc := X;
      begin
         X := Y;
         Y := Tmp;
      end Swap;
   end T2;

end P;
