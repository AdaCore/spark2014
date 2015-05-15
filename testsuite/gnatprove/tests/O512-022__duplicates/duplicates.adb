package body Duplicates is
   pragma SPARK_Mode (Off);  --  iterator on array

   procedure Dedupe (Arr: in out Int_Array; Last : out Natural) is
   begin
      Last := Arr'First;
      for New_Item in Arr'First + 1 .. Arr'Last loop

         --  Only increase Last and copy element if different from one already
         --  seen.

         if (for all Seen_Item in Arr'First .. Last =>
               Arr (New_Item) /= Arr (Seen_Item))
         then
            Last := Last + 1;
            Arr (Last) := Arr (New_Item);
         end if;

         pragma Loop_Invariant
           (not Has_Duplicates (Arr(Arr'First .. Last))
              and then
           (for all Item of Arr'Loop_Entry (Arr'First .. New_Item) =>
              (for some J in Arr'First .. Last => Item = Arr(J)))
              and then
           (for all J in Arr'First .. Last =>
              (for some Item of Arr'Loop_Entry => Item = Arr(J))));
      end loop;
   end Dedupe;

end Duplicates;
