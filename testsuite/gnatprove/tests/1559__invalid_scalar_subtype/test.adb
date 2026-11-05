with Ada.Unchecked_Conversion;

procedure Test with SPARK_Mode is
   type U is mod 256 with Size => 8;
   type P is range 0 .. 63 with Size => 8;
   subtype Wide is P'Base range 0 .. 127;
   subtype Same is P range 0 .. 63;
   subtype Narrow is P range 0 .. 31;

   function To_P is new Ada.Unchecked_Conversion (U, P)
     with Potentially_Invalid;

   procedure Test_Declaration is
      X : Wide := To_P (64) with Potentially_Invalid; -- @VALIDITY_CHECK:FAIL
   begin
      null;
   end Test_Declaration;

   procedure Test_Assignment is
      X : Wide := 0 with Potentially_Invalid;
   begin
      X := To_P (64); -- @VALIDITY_CHECK:FAIL
   end Test_Assignment;

   procedure Test_Valid_Result is
      X : Wide := To_P (32) with Potentially_Invalid;
   begin
      pragma Assert (X'Valid and then X = 32);
      X := To_P (16);
      pragma Assert (X'Valid and then X = 16);
   end Test_Valid_Result;

   procedure Test_Narrowing is
      X : Narrow := To_P (16) with Potentially_Invalid;
   begin
      X := To_P (32); -- @VALIDITY_CHECK:PASS @RANGE_CHECK:FAIL
   end Test_Narrowing;

   procedure Test_Matching_Subtypes is
      X : P := To_P (64) with Potentially_Invalid;
      Y : Same := To_P (64) with Potentially_Invalid;
   begin
      pragma Assert (not X'Valid and not Y'Valid);
      X := To_P (65);
      Y := To_P (65);
      pragma Assert (not X'Valid and not Y'Valid);
   end Test_Matching_Subtypes;

begin
   null;
end Test;
