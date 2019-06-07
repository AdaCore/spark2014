package body Generic_Interval_Tests
is

   procedure Test_01 (X, Y : FT;
                      Z    : out FT)
     with Pre => X in 0.0 .. 10.0 and
                 Y in 5.0 .. 10.0,
          Post => Z in 5.0 .. 20.0  -- ok
   is
   begin
      Z := X + Y;
   end Test_01;

   procedure Test_02 (X, Y : FT;
                      Z    : out FT)
     with Pre => X in 0.0 .. 10.0 and
                 Y in 5.0 .. 10.0,
          Post => Z in 10.0 .. 20.0  -- wrong
   is
   begin
      Z := X + Y;
   end Test_02;

   procedure Test_03 (X : FT)
     with Pre  => X * X in 0.0 .. 1.0,
          Post => X     in 0.0 .. 1.0  -- ok if FT is only positive
   is
   begin
      null;
   end Test_03;

   procedure Test_04 (X : FT)
     with Pre  => X     in 0.0 .. 1.0,
          Post => X * X in 0.0 .. 1.0  -- ok
   is
   begin
      null;
   end Test_04;

   procedure Test_05 (X : FT)
     with Pre  => X * abs X in 0.0 .. 1.0,
          Post => X         in 0.0 .. 1.0  -- ok
   is
   begin
      null;
   end Test_05;

   procedure Test_06 (X, Y : FT)
     with Pre  => Y >= 1.0,
          Post => X * Y >= X  -- ok
   is
   begin
      null;
   end Test_06;

   procedure Test_07 (X, Y : FT)
     with Pre  => Y > 1.0,
          Post => X * Y > X  -- wrong
   is
   begin
      null;
   end Test_07;

   procedure Test_08 (X, Y : FT)
     with Pre  => abs Y >= 1.0,
          Post => X / Y <= abs X  --  ok
   is
   begin
      null;
   end Test_08;

   procedure Test_09 (X, Y : FT)
     with Pre  => X in -5.0 .. 10.0 and
                  Y in -1.0 .. 10.0
   is
   begin
      if X * Y <= -30.0 then
         pragma Assert (X < 0.0);  --  ok
      end if;
   end Test_09;

   procedure Test_10 (X, Y : FT)
     with Pre  => X in -5.0 .. 10.0 and
                  Y in -1.0 .. 10.0
   is
   begin
      if X * Y <= -10.0 then
         pragma Assert (X < 0.0);  --  wrong
      end if;
   end Test_10;

   procedure Test_11 (X, Y : FT)
     with Pre  => X in -5.0 .. 10.0 and
                  Y in -1.0 .. 10.0
   is
   begin
      if X * Y < -10.0 then
         pragma Assert (X < 0.0);  --  ok
      end if;
   end Test_11;

   --  Crashes (see M921-002)
   --  procedure Test_12 (X, Y : FT;
   --                     Z    : out FT)
   --    with Pre  => X in -10.0 .. 10.0 and X not in -1.0 .. 1.0 and
   --                 Y in -10.0 .. 10.0,
   --         Post => Z not in  10.0 ..  11.0 and
   --                 Z not in -11.0 .. -10.0
   --  is
   --  begin
   --     Z := X + Y;
   --  end Test_12;

   --  Ditto
   --  procedure Test_13 (X, Y : FT;
   --                     Z    : out FT)
   --    with Pre  => X in -10.0 .. 10.0 and X < -1.0 and X > 1.0 and
   --                 Y in -10.0 .. 10.0,
   --         Post => Z not in  10.0 ..  11.0 and
   --                 Z not in -11.0 .. -10.0
   --  is
   --  begin
   --     Z := X + Y;
   --  end Test_13;

   procedure Test_14 (X : FT;
                      Z : out FT)
     with Pre  => (X in 1.0 .. 5.0) or (X in 10.0 .. 20.0),
          Post => (Z <= 6.0) xor (Z >= 11.0)  -- ok
   is
   begin
      Z := X + 1.0;
   end Test_14;

   procedure Test_15 (X : FT;
                      Z : out FT)
     with Pre  => (X in 0.0 .. 10.0) and (X in 5.0 .. 20.0),
          Post => Z in 10.0 .. 20.0   -- ok
   is
   begin
      Z := X * 2.0;
   end Test_15;

   procedure Test_16 (X : FT;
                      Z : out FT)
     with Pre  => (X in 0.0 .. 10.0) and (X in 5.0 .. 20.0),
          Post => Z > X  --  ok
   is
   begin
      Z := X * 2.0;
   end Test_16;

   procedure Test_17 (X : FT;
                      Z : out FT)
     with Pre  => (X in 0.0 .. 10.0) and (X in 5.0 .. 20.0),
          Post => Z > X  --  wrong
   is
   begin
      Z := (X * 2.0) - 5.0;
   end Test_17;

   procedure Test_18 (X : FT;
                      Z : out FT)
     with Pre  => (X in 0.0 .. 10.0) and (X in 5.0 .. 20.0),
          Post => Z >= X  --  ok
   is
   begin
      Z := (X * 2.0) - 5.0;
   end Test_18;

   procedure Test_19 (A, B, C, D : FT;
                      Z          : out FT)
     with Pre  => A in 0.0 .. 5.0 and
                  B in 5.0 .. 10.0 and
                  C in 4.0 .. 6.0 and
                  A < D and D < B and
                  C <= A and C >= B,
          Post => Z > 10.0              -- ok
   is
   begin
      pragma Assert (A < B);            -- ok
      pragma Assert (C = 5.0);          -- ok
      pragma Assert (D in 0.0 .. 10.0); -- ok
      Z := A + B + C + D;               -- ok
   end Test_19;



end Generic_Interval_Tests;
