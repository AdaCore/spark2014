procedure Renam2 is
   type Int_Acc is access Integer;
   X : Int_Acc := new Integer'(1);
   Y : Integer renames X.all;
begin
   X := new Integer'(2);
   pragma Assert (Y = 2);  -- this assertion fails
end;
