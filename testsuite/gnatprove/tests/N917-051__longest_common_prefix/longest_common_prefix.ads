package Longest_Common_Prefix
  with SPARK_Mode,
       Initializes => A
is
   type Text is array (Positive range <>) of Integer;
   A : Text (1 .. 1000) := (others => 0);

   function LCP (X, Y : Positive) return Natural
     with Pre  => X in A'Range and Y in A'Range,
          Post => (for all I in 0 .. LCP'Result  - 1 => A(X + I)= A(Y + I));

   function LCP2 (X, Y : Positive) return Natural
     with Pre  => X in A'Range and Y in A'Range,
          Post => (for all I in 0 .. LCP2'Result - 1 => A(I + X)= A(I + Y));

end Longest_Common_Prefix;
