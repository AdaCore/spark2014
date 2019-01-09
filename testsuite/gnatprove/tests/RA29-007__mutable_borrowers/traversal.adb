procedure Traversal with SPARK_Mode is
   type Int_Acc is access Integer;

   type Two_Acc is record
      Fst : Int_Acc;
      Snd : Int_Acc;
   end record;

   type Two_Acc_Acc is access Two_Acc;

   function Get_Fst (X : access Two_Acc) return access Integer is (X.Fst);

   function Id (X : Int_Acc) return access Integer is (X);

   V : Int_Acc := new Integer'(1);
   W : Int_Acc := new Integer'(2);
   X : Two_Acc_Acc := new Two_Acc'(V, W);
begin
   declare
      Y : access Integer := Get_Fst (X);
   begin
      Y.all := 4;
   end;

   pragma Assert (X.Fst.all = 1);
end Traversal;
