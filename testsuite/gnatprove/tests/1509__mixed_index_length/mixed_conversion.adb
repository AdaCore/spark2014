procedure Mixed_Conversion (N : Positive) with SPARK_Mode, Pre => N = 257 is
   type Byte is mod 256;
   type Arr is array (Positive range <>, Byte range <>) of Integer;
   A : Arr (1 .. N, 0 .. 0) := (others => (others => 0));
   subtype One is Arr (1 .. 1, 0 .. 0);

   --  The first dimension has length 257, not 1. Comparing its bounds in
   --  the second dimension's modular type would hide the mismatch.
   B : constant One := One (A); --  @LENGTH_CHECK:FAIL
begin
   pragma Assert (B (1, 0) = 0);
end Mixed_Conversion;
