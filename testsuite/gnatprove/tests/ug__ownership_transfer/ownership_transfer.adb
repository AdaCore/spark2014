procedure Ownership_Transfer with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   X   : Int_Ptr;
   Y   : Int_Ptr;
   Tmp : Integer;
begin
   X := new Integer'(1);
   X.all := X.all + 1;
   Y := X;
   Y.all := Y.all + 1;
   X.all := X.all + 1;  --  illegal
   X.all := 1;          --  illegal
   Tmp   := X.all;      --  illegal
end Ownership_Transfer;
