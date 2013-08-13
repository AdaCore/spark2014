package body Mergesort is
   -----------
   -- Merge --
   -----------
   procedure Merge (A                   : in     Our_Array;
                    ILeft, IRight, IEnd : in     Integer;
                    B                   : in out Our_Array)
   is
      I0, I1: Integer;
   begin
      I0 := ILeft;
      I1 := IRight;
      for J in Index_Range range ILeft .. IEnd - 1 loop
         if I0 < IRight
           and I1 = IEnd
         then
            --  Elements remain only in the first list.
            B (J) := A (I0);
            I0    := I0 + 1;
         elsif  I0 < IRight
           and I1 /= IEnd
           and A (I0) <= A (I1)
         then
            --  The head of the first list is smaller.
            B (J) := A (I0);
            I0    := I0 + 1;
         else
            --  Either elements remain only in the second list
            --  or the head of the second list is smaller.
            B (J) := A (I1);
            I1    := I1 + 1;
         end if;
      end loop;
   end Merge;

   ----------------
   -- Merge_Sort --
   ----------------
   procedure Merge_Sort (A : in out Our_Array) is
      Width, I : Integer;
      B        : Our_Array;
   begin
      Width := 1;
      B     := A;
      while Width <= Our_Array'Length loop
         I := Index_Range'First;
         while I <= Index_Range'Last loop
            Merge(A, I, Integer'Min (I + Width, Index_Range'Last + 1),
                  Integer'Min (I + 2 * Width, Index_Range'Last + 1), B);
            I := I + 2 * Width;
         end loop;
         A := B;
         Width := 2 * Width;
      end loop;
   end Merge_Sort;

end Mergesort;
