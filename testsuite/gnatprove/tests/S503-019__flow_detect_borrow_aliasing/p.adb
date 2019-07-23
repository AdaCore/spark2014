procedure Ownership_Transfer_At_Call with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   X : Int_Ptr;

   procedure Proc (Y : Int_Ptr)
     with Global => (In_Out => X)
   is
      Tmp : Integer;
   begin
      Y.all := Y.all + 1;
      X.all := X.all + 1;
   end Proc;

begin
   X := new Integer'(1);
   X.all := X.all + 1;
   Proc (X);  --  illegal
end Ownership_Transfer_At_Call;
