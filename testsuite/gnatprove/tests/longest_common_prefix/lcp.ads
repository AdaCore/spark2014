with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Natural with
  Pre  => X in A'Range and then Y in A'Range,
  Post =>
    (for all K in 0 .. LCP'Result - 1 => A (X + K) = A (Y + K))
      and then (X + LCP'Result = A'Last + 1
                  or else Y + LCP'Result = A'Last + 1
                  or else A (X + LCP'Result) /= A (Y + LCP'Result));
