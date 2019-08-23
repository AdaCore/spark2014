procedure Move_Const with SPARK_mode is
   type Int_Acc is access Integer;
   type R is record
      F : Int_Acc;
   end record;

   C : constant Int_Acc := new Integer'(34);
   X : constant R := (F => C);
begin
   X.F.all := 15;
end Move_Const;
