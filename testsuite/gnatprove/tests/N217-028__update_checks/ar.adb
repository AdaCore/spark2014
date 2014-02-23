package body AR is

   --  'Update, mix of choices
   --  5 falsifiable checks expected here.

   procedure Test1 (A: in out Arr1T; I, J: in IT1; E: in ET1)
   is
   begin
      A := A'Update (I - 1 | I .. J + 2 => E - 1, J + 1 => E + 1);
   end Test1;

   --  'Update, mix of choices
   --  5 valid checks expected here.

   procedure Test2 (A: in out Arr1T; I, J: in IT1; E: in ET1)
   is
   begin
      if I > IT1'First and J < IT1'First - 1 and E > ET1'First then
         A := A'Update (I - 1 | I .. J + 1 => E - 1, J + 2 => E + 1);
      end if;
   end Test2;

   ----------------------------------------------------
   -- Tests for checks in program bodies with 'Update
   ----------------------------------------------------

   --  Reference test for indexed component, for inspection of generated Why
   --  Falsifiable index check, Falsifiable range check

   procedure Test3 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      A (I + 1) := E - 1;
   end Test3;

   --  Reference test for indexed component
   --  Valid index check, Valid range check

   procedure Test4 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      if I < IT1'Last and E > ET1'First then
         A (I + 1) := E - 1;
      end if;
   end Test4;

   --  Reference test for normal aggregate, for inspecting generated Why.
   --  Valid Length check. One falsifiable range check (E - 1). No checks
   --  generated for E or choice ranges, these are statically analysed by
   --  the compiler to not need checks.

   procedure Test5 (A: out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      A := Arr1T'(1 .. 4 => E, 5 .. 10 => E - 1);
      A (I) := 5;
   end Test5;

   --  Reference test for normal aggregate with bogus dynamic choice: Valid
   --  range check (E - 1), one falsifiable length check, and one
   --  falsifiable range check (I + 1). Compiler analysis of the expanded
   --  code will report the bogus choice as a wrong length warning.

   procedure Test6 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      if I < IT1'Last and E > ET1'First then
         A := Arr1T'(I + 1 => E - 1);
      end if;
   end Test6;

   --  Simple 'Update
   --  No index check or range check generated, determined by compiler
   --  static analysis not to need checks.

   procedure Test7 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      A := A' Update (I => E);
   end Test7;

   --  Simple 'Update
   --  2 falsifiable range checks.

   procedure Test8 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      A := A' Update (I - 1 => E - 1);
   end Test8;

   --  Simple 'Update
   --  2 valid range checks.

   procedure Test9 (A: in out Arr1T; I: in IT1; E: in ET1)
   is
   begin
      if I < IT1'Last and E > ET1'First then
         A := A'Update (I + 1 => E - 1);
      end if;
   end Test9;

   --  'Update, choice is range,
   --  No index check or range check generated, determined by compiler
   --  static analysis not to need checks.

   procedure Test10 (A: in out Arr1T; I, J: in IT1; E: in ET1)
   is
   begin
      A := A' Update (I .. J => E);
   end Test10;

   --  'Update, choice is range,
   --  Three falsifiable range checks expected.

   procedure Test11 (A: in out Arr1T; I, J: in IT1; E: in ET1)
   is
   begin

      A := A' Update (I - 1 .. J + 1 => E - 1);
   end Test11;

   --  'Update, choice is list
   --  Three falsifiable range checks.

   procedure Test12 (A: in out Arr1T; I, J: in IT1; E: in ET1)
   is
   begin
      A := A' Update (I - 1 | J + 1 => E - 1);
   end Test12;

   --  'Update, choice is type range
   --  Falsifiable range check. No check generated for choice.

   procedure Test13 (A: in out Arr1T; E: in ET1)
   is
   begin
      A := A'Update (Arr1T'Range => E - 1);
   end Test13;

end AR;
