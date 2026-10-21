procedure Mixed_Assignment (N : Positive) with SPARK_Mode, Pre => N = 257 is
   type Byte is mod 256;
   type Arr is array (Positive range <>, Byte range <>) of Integer;
   A : Arr (1 .. N, 0 .. 0) := (others => (others => 0));
   B : Arr (1 .. 1, 0 .. 0);
begin
   --  Exercise the object-to-object length check as well as conversion
   B := A; --  @LENGTH_CHECK:FAIL
   pragma Assert (B (1, 0) = 0);
end Mixed_Assignment;
