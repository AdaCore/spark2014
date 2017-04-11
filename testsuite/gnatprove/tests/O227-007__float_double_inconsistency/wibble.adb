package body Wibble is

   type Float32 is new Float;
   type Float64 is new Long_Float;

   C : constant := 10.0;

   type U is mod 2**32;
   subtype T is U range 0 .. 1_000_000;

   procedure Test_01 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float32 (X) * (C + 1.0),
        Post => State <= Float32 (X + 1) * (C + 1.0)  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_01;

   procedure Test_02 (State : in out Float64;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float64 (X) * (C + 1.0),
        Post => State <= Float64 (X + 1) * (C + 1.0)  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_02;

   procedure Test_03 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float32 (X) * C,
        Post => State <= Float32 (X + 1) * C  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_03;

   procedure Test_04 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State in 0.0 | C .. Float32 (X) * C,
        Post => State in C .. Float32 (X + 1) * C  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_04;

   procedure Test_05 (State : in out Float64;
                      X     : T)
   with Pre => X < T'Last and
               State in 0.0 | C .. Float64 (X) * C,
        Post => State in C .. Float64 (X + 1) * C  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_05;


end Wibble;
