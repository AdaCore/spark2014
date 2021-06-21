procedure Test is
   type Int_Ptr is access Integer;
   X : Int_Ptr := new Integer'(10);
   Y : Int_Ptr;                --  Y is null by default
begin
   Y := X;                     --  ownership of X is transferred to Y
   pragma Assert (Y.all = 10); --  Y can be accessed
   Y.all := 11;                --  both for reading and writing
   pragma Assert (X.all = 11); --  but X cannot, or we would have an alias
end Test;
