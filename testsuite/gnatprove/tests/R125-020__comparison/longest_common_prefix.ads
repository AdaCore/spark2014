package Longest_Common_Prefix
  with SPARK_Mode => On,
  Initializes => A
is
   type Text is array (Positive range <>) of Integer;
   A : Text (1 .. 1000) := (others => 0);

   function LCP (X, Y : Positive) return Natural with
     Pre => (X in A'Range and Y in A'Range),

     Contract_Cases => (A (X) /= A (Y) => LCP'Result = 0,
                        X = Y => LCP'Result = A'Length - X + 1,
                        others => LCP'Result > 0),

     Post => (A (X .. X + LCP'Result - 1) = A (Y .. Y + LCP'Result - 1)
              and then
                (LCP'Result + X not in A'Range
                 or else LCP'Result + Y not in A'Range
                 or else A (X + LCP'Result) /= A (Y + LCP'Result)));
end Longest_Common_Prefix;
