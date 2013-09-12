package Duplicates is
   pragma SPARK_Mode (Off);  --  iterator on array
   type Int_Array is array (Natural range <>) of Integer;

   function Has_Duplicates(Arr : Int_Array) return Boolean is
      (for some I in Arr'First .. Arr'Last-1 =>
         (for some J in I+1 .. Arr'Last => Arr(I)=Arr(J)));

   procedure Dedupe (Arr: in out Int_Array; Last : out Natural) with
     Pre => Has_Duplicates(Arr),
     Post => not Has_Duplicates(Arr(Arr'First .. Last))
       and then (for all Item of Arr'Old =>
                   (for some J in Arr'First .. Last =>
                      Item = Arr(J)))
                -- Only duplicates removed
       and then (for all J in Arr'First .. Last =>
                   (for some Item of Arr'Old =>
                      Item = Arr(J)));
                -- Nothing new added

end Duplicates;
