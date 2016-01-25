procedure ASlice
with
   SPARK_Mode
is
   type M64_Type is mod 2**64;
   type X_Type is array (M64_Type range <>) of Integer;

   A : X_Type (0 .. 1000) := (others => 42);
   B : X_Type (10 .. 20) := (others => 1);
begin
   A (10 .. 20) := B;
end ASlice;
