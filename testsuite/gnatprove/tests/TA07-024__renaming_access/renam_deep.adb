procedure Renam_Deep is
   type Int_Acc is access Integer;
   type Int_Acc_Acc is access Int_Acc;
   X : Int_Acc := new Integer'(1);
   Y : Int_Acc_Acc := new Int_Acc'(X);
   Z : Integer renames Y.all.all;
begin
   Y.all := new Integer'(2);
   pragma Assert (Z = 2);  -- this assertion fails
end;
