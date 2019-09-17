procedure Ptr with SPARK_Mode is
   type Int_Ptr is access Integer;
   X : Int_Ptr := new Integer'(0);
begin
   declare
      Y : access Integer := X;
   begin
      Y.all := 42;
   end;
   declare
      Z : access Integer := Int_Ptr'(X);
   begin
      Z.all := 42;
   end;
end Ptr;
