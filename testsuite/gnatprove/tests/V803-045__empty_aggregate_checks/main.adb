pragma Extensions_Allowed (On);
with Interfaces; use Interfaces;
procedure Main with SPARK_Mode is

   --  Static range check on empty array indexed by signed integers
   procedure P1 with
     Global => null
   is
      type T is array (Integer range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P1;

   --  OK empty array indexed by signed integers
   procedure P2 with
     Global => null
   is
      type My_Nat is new Natural;
      type T is array (My_Nat range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P2;

   --  Dynamic range check on empty array indexed by signed integers
   procedure P3 (CCC : Integer) with
     Global => null
   is
      type My_Nat is new Integer range CCC .. Integer'Last;
      type T is array (My_Nat range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P3;

   --  Empty array indexed by signed integers with fixed lower bound
   procedure P4 with
     Global => null
   is
      type T is array (Integer range 0 .. <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P4;

   --  Static range check on empty array indexed by modular integers
   procedure P5 with
     Global => null
   is
      type T is array (Unsigned_16 range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P5;

   --  OK empty array indexed by modular integers
   procedure P6 with
     Global => null
   is
      subtype My_Pos is Unsigned_16 range 1 .. Unsigned_16'Last;
      type T is array (My_Pos range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P6;

   --  Dynamic range check on empty array indexed by modular integers
   procedure P7 (CCC : Unsigned_16) with
     Global => null
   is
      subtype My_Pos is Unsigned_16 range CCC .. Unsigned_16'Last;
      type T is array (My_Pos range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P7;

   --  Empty array indexed by modular integers with fixed lower bound
   procedure P8 with
     Global => null
   is
      type T is array (Unsigned_16 range 1 .. <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P8;

   type Index is (A, B, C, D, E);

   --  Static range check on empty array indexed by an enumeration
   procedure P9 with
     Global => null
   is
      type T is array (Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P9;

   --  OK empty array indexed by an enumeration
   procedure P10 with
     Global => null
   is
      subtype My_Index is Index range B .. E;
      type T is array (My_Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P10;

   --  Dynamic range check on empty array indexed by an enumeration
   procedure P11 (CCC : Index) with
     Global => null
   is
      type My_Index is new Index range CCC .. E;
      type T is array (My_Index range <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P11;

   --  Empty array indexed by an enumeration with fixed lower bound
   procedure P12 with
     Global => null
   is
      type T is array (Index range B .. <>) of Integer;
      X : T := [];  --  @RANGE_CHECK:PASS
   begin
      null;
   end P12;

begin
   null;
end Main;
