with Types; use Types;

----------------------------------------------------
-- SPARK 2014 - Longest_Common_Prefix Example     --
--                                                --
-- The body of this function illustrates the use  --
-- of loop invariant and variant pragmas in       --
-- SPARK 2014.                                    --
----------------------------------------------------

function LCP (A : Text; X, Y : Integer) return Natural
  with SPARK_Mode
is
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
