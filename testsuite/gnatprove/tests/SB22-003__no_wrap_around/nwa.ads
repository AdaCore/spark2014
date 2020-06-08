package NWA with SPARK_Mode is

   type NvU8 is mod 2**8
     with Annotate => (GNATprove, No_Wrap_Around);

   type NvU16 is mod 2**16
     with Annotate => (GNATprove, No_Wrap_Around);

   type NvU32 is mod 2**32
     with Annotate => (GNATprove, No_Wrap_Around);

   type NvU64 is mod 2**64
     with Annotate => (GNATprove, No_Wrap_Around);

   procedure Test8 (X, Y : NvU8) with Global => null;
   procedure Pass8 (X, Y : NvU8) with Global => null,
     Pre => X <= NvU8'Last / 2 and Y <= X and Y in 1 .. 2;

   procedure Test16 (X, Y : NvU16) with Global => null;
   procedure Pass16 (X, Y : NvU16) with Global => null,
     Pre => X <= NvU16'Last / 4 and Y <= X and Y in 1 .. 4;

   procedure Test32 (X, Y : NvU32) with Global => null;
   procedure Pass32 (X, Y : NvU32) with Global => null,
     Pre => X <= NvU32'Last / 42 and Y <= X and Y in 1 .. 42;

   procedure Test64 (X, Y : NvU64) with Global => null;
   procedure Pass64 (X, Y : NvU64) with Global => null,
     Pre => X <= 2**32-1 and Y <= X and Y in 1 .. 2**32;

   type NvU17 is mod 17
     with Annotate => (GNATprove, No_Wrap_Around);

   procedure Test17 (X, Y : NvU17) with Global => null;
   procedure Pass17 (X, Y : NvU17) with Global => null,
     Pre => X <= NvU17'Last / 2 and Y <= X and Y in 1 .. 2;

   type NvU16b is new NvU16;

   procedure Test16b (X, Y : NvU16b) with Global => null;
   procedure Pass16b (X, Y : NvU16b) with Global => null,
     Pre => X <= NvU16b'Last / 4 and Y <= X and Y in 1 .. 4;

   type NvU32b is new NvU32 range 0 .. 1000;

   procedure Test32b (X, Y : NvU32b) with Global => null;
   procedure Pass32b (X, Y : NvU32b) with Global => null,
     Pre => X <= NvU32b'Last / 42 and Y <= X and Y in 1 .. 42;

   type NvU64a is mod 2**64;
   type NvU64c is new NvU64a
     with Annotate => (GNATprove, No_Wrap_Around);
   type NvU64b is new NvU64c;

   procedure Test64b (X, Y : NvU64b) with Global => null;
   procedure Pass64b (X, Y : NvU64b) with Global => null,
     Pre => X <= 2**32-1 and Y <= X and Y in 1 .. 2**32;

end NWA;
