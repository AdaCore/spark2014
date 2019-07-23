package body Swap_Ranges with
     Spark_Mode is

   procedure Swap_Ranges_With_Error (A : in out T_Arr; B : in out T_Arr) is
      Temp : T;
      K, L : Positive;
   begin

      for J in 0 .. A 'Length - 1 loop
         L := B'First + J;
         K := A'First + J;
         Temp  := A (K);
         A (K) := B (L);
         B (L) := Temp;
         pragma Loop_Invariant
           (B'Loop_Entry (B'First .. L) = A (A'First .. K)); --@LOOP_INVARIANT_PRESERV:FAIL
         pragma Loop_Invariant
           (A'Loop_Entry (A'First .. K) = B (B'First .. L)); -- provable from the previous one
         pragma Loop_Invariant
           (if
              L < B'Last
            then
               B'Loop_Entry (L + 1 .. B'Last) = B (L + 1 .. B'Last)); --@LOOP_INVARIANT_PRESERV:FAIL
         pragma Loop_Invariant
           (if
              K < A'Last
            then
               A'Loop_Entry (K + 1 .. A'Last) = A (K + 1 .. A'Last)); -- provable from the previous one
      end loop;
   end Swap_Ranges_With_Error;

   procedure Swap_Ranges_Without_Error (A : in out T_Arr; B : in out T_Arr) is
      Temp : T;
   begin

      for J in 0 .. A'Length - 1 loop
         Temp            := A (A'First + J);
         A (A'First + J) := B (B'First + J);
         B (B'First + J) := Temp;

         pragma Loop_Invariant
           (B'Loop_Entry (B'First .. B'First + J) =
            A (A'First .. A'First + J));
         pragma Loop_Invariant
           (A'Loop_Entry (A'First .. A'First + J) =
            B (B'First .. B'First + J));
         pragma Loop_Invariant
           (if
              B'First + J < B'Last
            then
              B'Loop_Entry (B'First + J + 1 .. B'Last) =
              B (B'First + J + 1 .. B'Last));
         pragma Loop_Invariant
           (if
              A'First + J < A'Last
            then
              A'Loop_Entry (A'First + J + 1 .. A'Last) =
              A (A'First + J + 1 .. A'Last));

      end loop;
   end Swap_Ranges_Without_Error;

end Swap_Ranges;
