procedure Deep_Globals with SPARK_Mode is
   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(34);
   Z : Integer;

   procedure P with Pre => X /= null is
   begin
      Z := X.all;
   end P;

   procedure Q with Pre => X /= null is
   begin
      X.all := Z;
   end Q;

begin
   P;
   Q;
end Deep_Globals;
