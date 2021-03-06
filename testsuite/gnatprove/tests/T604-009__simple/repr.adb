procedure Repr with SPARK_Mode is
   type U64 is mod 2**64;

   procedure Insert (Val : U64)
      with Pre => Val < U64'Last - 1
   is
      LSE_Value : constant Short_Integer := U64'Pos (Val) mod 256; --@RANGE_CHECK:FAIL
   begin
      null;
   end Insert;

begin
   Insert (12297829382473034410);
end Repr;
