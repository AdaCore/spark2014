package body Incr_Loop is

   procedure Iter (A : in out Arr_Type) is
   begin
      for I in A'Range loop
         pragma Loop_Invariant
            ((for all K in A'First .. I - 1 =>
               A (K) = A'Loop_Entry (K) + 1)
             and
             (for all K in I .. A'Last  =>
               A (K) = A'Loop_Entry (K)));
         A (I) := A (I) + 1;
      end loop;
   end Iter;

end Incr_Loop;
