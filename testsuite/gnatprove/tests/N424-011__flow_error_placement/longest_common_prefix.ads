package Longest_Common_Prefix
  with SPARK_Mode => On,
  Initializes => A
is
   type Text is array (Positive range <>) of Integer;
   A : Text (1 .. 1000) := (others => 0);

   function LCP (X, Y : Positive) return Natural;

end Longest_Common_Prefix;
