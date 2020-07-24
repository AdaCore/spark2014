procedure Ownership_Borrowing with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   X   : Int_Ptr := new Integer'(1);
   Tmp : Integer;
begin
   declare
      B : access Integer := X;
   begin
      B.all := B.all + 1;
      X.all := X.all + 1;  --  illegal
      X.all := 1;          --  illegal
      Tmp   := X.all;      --  illegal
   end;
   X.all := X.all + 1;
   X.all := 1;
   Tmp   := X.all;
end Ownership_Borrowing;
