package body Longest_Common_Prefix
  with SPARK_Mode
is

   --  LCP and LCP2 are identical

   function LCP (X, Y : Positive) return Natural is
      L : Natural;
   begin
      L := 0;
      while X + L <= A'Last
        and then Y + L <= A'Last
        and then A (X + L) = A (Y + L)
      loop
         pragma Loop_Invariant (for all K in 0 .. L - 1 => A (X + K) = A (Y + K));
         pragma Loop_Variant (Increases => L);
         L := L + 1;
      end loop;
      return L;
   end LCP;

   function LCP2 (X, Y : Positive) return Natural is
      L : Natural;
   begin
      L := 0;
      while X + L <= A'Last
        and then Y + L <= A'Last
        and then A (X + L) = A (Y + L)
      loop
         pragma Loop_Invariant (for all K in 0 .. L - 1 => A (X + K) = A (Y + K));
         pragma Loop_Variant (Increases => L);
         L := L + 1;
      end loop;
      return L;
   end LCP2;

end Longest_Common_Prefix;
