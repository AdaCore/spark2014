procedure Test is
   type Int_Ptr is access Integer;
   X   : Int_Ptr := new Integer'(10);
   Tmp : Int_Ptr := X; --  ownership of X is moved to Tmp
                       --  X cannot be accessed.
begin
   X.all := 0;
end Test;
