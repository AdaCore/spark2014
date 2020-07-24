procedure Ownership_Observing with
  SPARK_Mode
is
   type Int_Ptr is access Integer;
   X   : Int_Ptr := new Integer'(1);
   Tmp : Integer;
begin
   declare
      B : access constant Integer := X;
   begin
      Tmp   := B.all;
      Tmp   := X.all;
      X.all := X.all + 1;  --  illegal
      X.all := 1;          --  illegal
   end;
   X.all := X.all + 1;
   X.all := 1;
   Tmp   := X.all;
end Ownership_Observing;
