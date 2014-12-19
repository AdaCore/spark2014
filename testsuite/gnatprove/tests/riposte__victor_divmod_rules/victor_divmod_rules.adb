package body Victor_DivMod_Rules
is
   pragma Warnings (Off, "* has no effect");

   type T is range -1000 .. 1000;

   --  divmod(1):   0 <= X mod Y  may_be_deduced_from [0 < Y].
   procedure DivMod_01 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 < Y,
          Post    => 0 <= X mod Y  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_01;

   --  divmod(2):   X mod Y < Y   may_be_deduced_from [0 < Y].
   procedure DivMod_02 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 < Y,
          Post    => X mod Y < Y  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_02;

   --  divmod(3):   X mod Y <= 0  may_be_deduced_from [Y < 0].
   procedure DivMod_03 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => Y < 0,
          Post    => X mod Y <= 0  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_03;

   --  divmod(4):   Y < X mod Y   may_be_deduced_from [Y < 0].
   procedure DivMod_04 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => Y < 0,
          Post    => Y < X mod Y
   is
   begin
      null;
   end DivMod_04;

   ------------------------------------------------------------------------------
   --  X/Y - 1 < X div Y <= X/Y  if X >= 0, Y > 0
   ------------------------------------------------------------------------------

   --  divmod(5):   X - Y < Y * (X div Y)  may_be_deduced_from [0 <= X, 0 < Y].
   procedure DivMod_05 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and 0 < Y,
          Post    => X - Y < Y * (X / Y)  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_05;

   --  divmod(6):   Y * (X div Y) <= X     may_be_deduced_from [0 <= X, 0 < Y].
   procedure DivMod_06 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and 0 < Y,
          Post    => Y * (X / Y) <= X  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_06;

   ------------------------------------------------------------------------------
   --  X/Y  <= X div Y < X/Y + 1   if X <= 0, Y > 0
   ------------------------------------------------------------------------------

   --  FS Notes that the top comment has a X/Y + 1 and rule 8 does not.

   --  divmod(7):   X <= Y * (X div Y)     may_be_deduced_from [X <= 0, 0 < Y].
   procedure DivMod_07 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and 0 < Y,
          Post    => X <= Y * (X / Y)  --  @POSTCONDITION:PASS
   is
   begin
      --# accept F, 30, X, "Ok"& F, 30, Y, "Ok";
      null;
   end DivMod_07;

   --  divmod(8):   Y * (X div Y) < X + Y  may_be_deduced_from [X <= 0, 0 < Y].
   procedure DivMod_08 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and 0 < Y,
          Post    => Y * (X / Y) < X + Y  --  @POSTCONDITION:PASS
   is
   begin
      --# accept F, 30, X, "Ok"& F, 30, Y, "Ok";
      null;
   end DivMod_08;

   ------------------------------------------------------------------------------
   --  X/Y  <= X div Y < X/Y + 1  if X >= 0, Y < 0
   ------------------------------------------------------------------------------

   --  divmod(9):   X >= Y * (X div Y)     may_be_deduced_from [0 <= X, Y < 0].
   procedure DivMod_09 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and Y < 0,
          Post    => X >= Y * (X / Y)  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_09;

   --  divmod(10):   Y * (X div Y) > X + Y  may_be_deduced_from [0 <= X, Y < 0].
   procedure DivMod_10 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and Y < 0,
          Post    => Y * (X / Y) > X + Y  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_10;

   ------------------------------------------------------------------------------
   --  X/Y - 1 < X div Y <= X/Y  if X <= 0, Y < 0
   ------------------------------------------------------------------------------

   --  divmod(11):   X - Y > Y * (X div Y)     may_be_deduced_from [X <= 0, Y < 0].
   procedure DivMod_11 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and Y < 0,
          Post    => X - Y > Y * (X / Y)  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_11;

   --  divmod(12):  Y * (X div Y) >= X         may_be_deduced_from [X <= 0, Y < 0].
   procedure DivMod_12 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and Y < 0,
          Post    => Y * (X / Y) >= X  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_12;

   ------------------------------------------------------------------------------
   --  Other, ungrouped rules
   ------------------------------------------------------------------------------

   --  divmod(13):  Y * (X div Y) + int___rem(X, Y) = X may_be_deduced_from [Y <> 0].
   procedure DivMod_13 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => Y /= 0,
          Post    => Y * (X / Y) + (X rem Y) = X  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_13;

   --  divmod(14):  X mod Y = 0 may_be_deduced_from [int___rem(X, Y) = 0].
   procedure DivMod_14 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X rem Y = 0,
          Post    => X mod Y = 0
   is
   begin
      null;
   end DivMod_14;

   --  divmod(15):  X mod Y = int___rem(X, Y) may_be_deduced_from [0 <= X, 0 < Y].
   procedure DivMod_15 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and 0 < Y,
          Post    => X mod Y = X rem Y
   is
   begin
      null;
   end DivMod_15;

   --  divmod(16):  X mod Y = int___rem(X, Y) + Y may_be_deduced_from [X <= 0, 0 < Y, int___rem(X, Y) <> 0].
   procedure DivMod_16 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and 0 < Y and X rem Y /= 0,
          Post    => X mod Y = X rem Y + Y
   is
   begin
      null;
   end DivMod_16;

   --  divmod(17):  X mod Y = int___rem(X, Y) + Y may_be_deduced_from [0 <= X, Y < 0, int___rem(X, Y) <> 0].
   procedure DivMod_17 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and Y < 0 and X rem Y /= 0,
          Post    => X mod Y = X rem Y + Y
   is
   begin
      null;
   end DivMod_17;

   --  divmod(18):  X mod Y = int___rem(X, Y) may_be_deduced_from [X <= 0, Y < 0].
   procedure DivMod_18 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => X <= 0 and Y < 0,
          Post    => X mod Y = X rem Y
   is
   begin
      null;
   end DivMod_18;

   --  FS: Where did rule 19 go to?

   --  PJ writes: divmod(20) Is deducible by Z3, but its performance
   --  is much better with this explicit.

   --  divmod(20):  X mod Y = X may_be_deduced_from [0 <= X, X < Y].
   procedure DivMod_20 (X, Y : in T)
     with Depends => (null => (X, Y)),
          Pre     => 0 <= X and X < Y,
          Post    => X mod Y = X  --  @POSTCONDITION:PASS
   is
   begin
      null;
   end DivMod_20;

   pragma Warnings (On, "* has no effect");
end Victor_DivMod_Rules;
