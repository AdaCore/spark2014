with Types; use Types;

function LCP (A : Text; X, Y : Integer) return Natural with
  SPARK_Mode,
  Pre  => X in A'Range and then Y in A'Range,
  Post =>
     A (X .. X + LCP'Result - 1) = A (Y .. Y + LCP'Result - 1)
     and then (X + LCP'Result = A'Last + 1
                 or else Y + LCP'Result = A'Last + 1
                 or else A (X + LCP'Result) /= A (Y + LCP'Result)),
  Contract_Cases =>
     (A (X) /= A (Y) => LCP'Result = 0,
      X = Y          => LCP'Result = A'Last - X + 1,
      others         => LCP'Result > 0);
