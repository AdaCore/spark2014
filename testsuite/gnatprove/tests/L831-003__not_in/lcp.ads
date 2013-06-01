with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Integer with
  Pre  => X in A'Range and then Y in A'Range,
  Post =>
    (for all K in 0 .. LCP'Result => A (X + K) = A (Y + K))
      and then (X + LCP'Result not in A'Range
                  or else Y + LCP'Result not in A'Range
                  or else A (X + LCP'Result) /= A (Y + LCP'Result));
