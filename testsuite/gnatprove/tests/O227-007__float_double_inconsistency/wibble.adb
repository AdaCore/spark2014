package body Wibble is

   type Float32 is new Float;
   type Float64 is new Long_Float;

   C : constant := 10.0;

   type T is range 0 .. 1_000_000;

   --  Each of these I have verified manually.

   --  Original customer test, this goes through SPARK OK right now.
   procedure Test_01 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float32 (X) * (C + 1.0),
        Post => State <= Float32 (X + 1) * (C + 1.0)  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_01;

   --  .. but not for doubles.
   --  Takes 33s to check
   procedure Test_02 (State : in out Float64;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float64 (X) * (C + 1.0),
        Post => State <= Float64 (X + 1) * (C + 1.0)  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_02;

   --  They should not need the extra 1.0
   --  Takes 7.7s to check
   procedure Test_03 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State <= Float32 (X) * C,
        Post => State <= Float32 (X + 1) * C  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_03;

   --  Its better to use a punctured interval
   --  Takes 0.02s to check
   procedure Test_04 (State : in out Float32;
                      X     : T)
   with Pre => X < T'Last and
               State in 0.0 | C .. Float32 (X) * C,
        Post => State in C .. Float32 (X + 1) * C  -- ok
   is
   begin
      State := State + C;  -- ok
   end Test_04;

   --  And it should also work for doubles
   --  Takes 0.034s to check
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
