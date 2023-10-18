procedure Main with SPARK_Mode is

   --  There must be a failed check if upper bound computation wraparound
   --  with a modular index type

   procedure Bad_Wraparound is
      type M is mod 6;
      type W is array (M range <>) of Integer;

      function Dice_Roll return M is (4);

      X             : constant M              := Dice_Roll;
      Prefix        : constant W (X .. X + 1) := (2, 7); --@RANGE_CHECK:PASS
      Spark_Weights : constant W (X .. X + 2) := (2, 7, 13); --@RANGE_CHECK:FAIL
   begin
      null;
   end Bad_Wraparound;

   --  There must be a failed check if the number of positional association
   --  before the 'others' choice may exceed the total capacity of the array.

   procedure Excessive_Elements_Before_Others_1 (X : Natural) is
      subtype I is Integer range 0 .. X;
      type W is array (I) of Integer;
      Y : constant W :=  (2, others => 7); --@RANGE_CHECK:PASS
      Z : constant W := (2, 7, others => 13); --@RANGE_CHECK:FAIL
   begin
      null;
   end Excessive_Elements_Before_Others_1;

   --  Variant for modular types

   procedure Excessive_Elements_Before_Others_2 is
      type M is mod 6;
      type W is array (M range <>) of Integer;
      function Dice_Roll return M is (1);
      X : constant M := Dice_Roll;
      Y : constant W (X .. X + 2) := (2, 7, others => 13); --@RANGE_CHECK:PASS
      Z : constant W (X .. X) := (2, 7, others => 13); --@RANGE_CHECK:FAIL
   begin
      null;
   end Excessive_Elements_Before_Others_2;

   --  Second Variant for modular types, check that wraparound is handled
   --  properly.

   procedure Excessive_Elements_Before_Others_3 is
      type M is mod 6;
      type W is array (M range <>) of Integer;
      function Dice_Roll return M is (4);
      X : constant M := Dice_Roll;
      Y : constant W (X .. X + 1) := (2, 7); --@RANGE_CHECK:PASS
      Z : constant W (X .. X + 1) := (2, 7, 13, others => 42); --@RANGE_CHECK:FAIL
   begin
      null;
   end Excessive_Elements_Before_Others_3;

begin
   null;
end Main;
