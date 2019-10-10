procedure Locate_Checks with SPARK_Mode is
   type Int_Acc is access Integer;

   X : Int_Acc := new Integer'(34);
   Z : Integer;

   procedure P with Global => (Input => X, Output => Z) is
   begin
      Z := X.all;
   end P;

   Y : Int_Acc := X;
begin
   P;
end Locate_Checks;
