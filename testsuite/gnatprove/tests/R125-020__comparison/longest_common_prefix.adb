package body Longest_Common_Prefix
with SPARK_Mode => On
is
   function LCP (X, Y : Positive) return Natural is
      L : Natural;
   begin
      L := 0;

      while X + L <= A'Last
        and then Y + L <= A'Last
        and then A (X + L) = A (Y + L)
      loop
         pragma Loop_Invariant
           (A (X .. X + L) = A (Y .. Y + L));
         --pragma Loop_Invariant
         --  (for all I in 0 .. L => A (X + I) = A (Y + I));
         pragma Loop_Variant (Increases => L);
         L := L + 1;
      end loop;

      return L;
   end LCP;

end Longest_Common_Prefix;
