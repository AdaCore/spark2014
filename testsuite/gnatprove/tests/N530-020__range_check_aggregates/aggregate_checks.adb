package body Aggregate_Checks with SPARK_Mode is

   procedure Do_Wrong_Aggregate (A : Nat_Array) is
      subtype A_Range is Positive range A'Range;

      type Wrapper is record
         Content : A_Range;
      end record;

      Should_Fail : constant Wrapper := (Content => 0); --  @RANGE_CHECK:FAIL
   begin
      null;
   end Do_Wrong_Aggregate;

   procedure Do_Wrong_Aggregate_2 (A : Nat_Array) is
      subtype A_Range is Positive range A'Range;
      type Wrapper2 is array (1 .. 1) of A_Range;

      Should_Fail2 : constant Wrapper2 := (1 => 0); --  @RANGE_CHECK:FAIL
   begin
      null;
   end Do_Wrong_Aggregate_2;

   procedure Do_Wrong_Aggregate_3 (A : Nat_Array) is
      subtype A_Range is Positive range A'Range;
      type Wrapper3 is array (1 .. 2) of A_Range;

      Should_Fail22 : constant Wrapper3 := (1 => 1, 2 => 0); --  @RANGE_CHECK:FAIL
   begin
      null;
   end Do_Wrong_Aggregate_3;

   procedure Do_Wrong_Aggregate_4 (A : Nat_Array) is
      subtype A_Range is Positive range A'Range;
      type UArray is array (A_Range range <>) of Natural;

      Should_Fail3 : constant UArray := (0 .. A'Last => 0); --  @RANGE_CHECK:FAIL
   begin
      null;
   end Do_Wrong_Aggregate_4;
end;
