procedure Deep_Globals with SPARK_Mode is
   type Int_Acc is access Integer;

   type Int_Acc_Acc is access Int_Acc;

   C2 : constant Int_Acc := new Integer'(34);
   X2 : Int_Acc_Acc := new Int_Acc'(C2);
   Z2 : Int_Acc;

   procedure P2 with Pre => X2 /= null is
   begin
      Z2 := X2.all;
   end P2;

   procedure Q2 with Pre => X2 /= null is
   begin
      X2.all := Z2;
   end Q2;

begin
   P2;
   Q2;
end Deep_Globals;
