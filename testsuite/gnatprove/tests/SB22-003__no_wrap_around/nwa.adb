package body NWA with SPARK_Mode is

   procedure Test8 (X, Y : NvU8) is
      Z : NvU8;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test8;

   procedure Pass8 (X, Y : NvU8) is
      Z : NvU8;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass8;

   procedure Test16 (X, Y : NvU16) is
      Z : NvU16;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test16;

   procedure Pass16 (X, Y : NvU16) is
      Z : NvU16;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass16;

   procedure Test32 (X, Y : NvU32) is
      Z : NvU32;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test32;

   procedure Pass32 (X, Y : NvU32) is
      Z : NvU32;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass32;

   procedure Test64 (X, Y : NvU64) is
      Z : NvU64;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test64;

   procedure Pass64 (X, Y : NvU64) is
      Z : NvU64;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass64;

   procedure Test17 (X, Y : NvU17) is
      Z : NvU17;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test17;

   procedure Pass17 (X, Y : NvU17) is
      Z : NvU17;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass17;

   procedure Test16b (X, Y : NvU16b) is
      Z : NvU16b;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test16b;

   procedure Pass16b (X, Y : NvU16b) is
      Z : NvU16b;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass16b;

   procedure Test32b (X, Y : NvU32b) is
      Z : NvU32b;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS RANGE_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS RANGE_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test32b;

   procedure Pass32b (X, Y : NvU32b) is
      Z : NvU32b;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass32b;

   procedure Test64b (X, Y : NvU64b) is
      Z : NvU64b;
   begin
      Z := + X;
      Z := X * Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X / Y;  --  @DIVISION_CHECK:FAIL
      Z := X + Y;  --  @OVERFLOW_CHECK:FAIL
      Z := X - Y;  --  @OVERFLOW_CHECK:FAIL
      Z := - X;  --  @OVERFLOW_CHECK:FAIL
   end Test64b;

   procedure Pass64b (X, Y : NvU64b) is
      Z : NvU64b;
   begin
      if X = 0 then
         Z := - X;  --  @OVERFLOW_CHECK:PASS
      end if;
      Z := + X;
      Z := X + Y;  --  @OVERFLOW_CHECK:PASS
      Z := X - Y;  --  @OVERFLOW_CHECK:PASS
      Z := X * Y;  --  @OVERFLOW_CHECK:PASS
      Z := X / Y;  --  @DIVISION_CHECK:PASS
   end Pass64b;

end NWA;
