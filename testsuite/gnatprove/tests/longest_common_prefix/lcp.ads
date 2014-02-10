with Types; use Types;

----------------------------------------------------
-- SPARK 2014 - Longest_Common_Prefix Example     --
--                                                --
-- This example illustrates the use of Pre, Post  --
-- and Contract_Cases aspects in SPARK 2014.      --
----------------------------------------------------

function LCP (A : Text; X, Y : Integer) return Natural with
  SPARK_Mode,
  Pre  => X in A'Range and then Y in A'Range,
  Post =>
    (for all K in 0 .. LCP'Result - 1 => A (X + K) = A (Y + K))
      and then (X + LCP'Result = A'Last + 1
                  or else Y + LCP'Result = A'Last + 1
                  or else A (X + LCP'Result) /= A (Y + LCP'Result)),
  Contract_Cases =>
     (A (X) /= A (Y) => LCP'Result = 0,
      X = Y          => LCP'Result = A'Last - X + 1,
      others         => LCP'Result > 0);
