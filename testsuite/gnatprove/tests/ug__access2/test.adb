procedure Test is
   type Int_Ptr is access Integer;
   X : Int_Ptr := new Integer'(10);
   Y : Int_Ptr;        --  Y is null by default
   Tmp : Int_Ptr := X; --  ownership of X is moved to Tmp
                       --  X cannot be accessed.
begin
   X := Y; --  ownership of Y is moved to X
           --  Y cannot be accessed
           --  X has full ownership.
   Y := Tmp; --  ownership of Tmp is moved to Y
             --  Tmp cannot be accessed
             --  Y has fullownership.
end Test;
