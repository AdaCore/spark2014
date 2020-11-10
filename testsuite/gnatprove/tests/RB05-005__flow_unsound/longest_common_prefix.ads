package Longest_Common_Prefix
  with Initializes => A
is
   type Text is array (Positive range <>) of Integer;
   A : Text (1 .. 1000) := (others => 0);

   function LCP (X, Y : Positive) return Natural
   with Pre => X in A'Range and Y in A'Range;

end Longest_Common_Prefix;
