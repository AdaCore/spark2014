package body Reverse_Ord
  with SPARK_Mode
is
   type Array_Of_Int is array (1 .. 10) of Integer;

   procedure Reverse_Order (A : in out Array_Of_Int)
     with Post => (for all J in A'Range => A (J) = A'Old (A'Last - J + 1) and
                     A (A'Last - J + 1) = A'Old (J))
   is
      Temp : Integer;
   begin
      for Index in A'First .. (A'Last + 1) / 2 loop
         Temp := A (Index);
         A (Index) := A (A'Last - Index + 1);
         A (A'Last - Index + 1) := Temp;
         pragma Loop_Invariant
           (-- Elements that have been visited so far are swapped
            (for all J in A'First .. Index =>
               A (J) = A'Loop_Entry (A'Last - J + 1) and
               A (A'Last - J + 1) = A'Loop_Entry (J))
              and then
              -- Elements not yet visited are unchanged
              (for all J in Index + 1 .. A'Last - Index =>
                 A (J) = A'Loop_Entry (J)));

      end loop;
   end Reverse_Order;
end Reverse_Ord;
