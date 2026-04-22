pragma Ada_2022;

with Ada.Unchecked_Conversion;
with Interfaces; use Interfaces;

procedure Test with SPARK_Mode is

   type R_Valid is record
      F : Unsigned_8;
   end record;

   type R_Invalid_1 is record
      F : Boolean;
   end record;

   subtype Nat_8 is Integer_8 range 0 .. Integer_8'Last;
   type R_Invalid_2 is record
      F : Nat_8;
   end record;

   function R_Valid_To_Invalid_1 is new Ada.Unchecked_Conversion (R_Valid, R_Invalid_1) with Potentially_Invalid;
   function R_Invalid_1_To_Valid is new Ada.Unchecked_Conversion (R_Invalid_1, R_Valid);

   procedure Test_1 (X : R_Valid) is
   begin
      pragma Assert
        (if R_Valid_To_Invalid_1 (X)'Valid_Scalars
         then X = R_Invalid_1_To_Valid (R_Valid_To_Invalid_1 (X)));
      pragma Assert
        (R_Valid_To_Invalid_1 (X)'Valid_Scalars); --  ASSERT:FAIL
   end Test_1;

   procedure Test_2 (X : R_Invalid_1) is
   begin
      pragma Assert
        (R_Valid_To_Invalid_1 (R_Invalid_1_To_Valid (X))'Valid_Scalars);
      pragma Assert
        (X = R_Valid_To_Invalid_1 (R_Invalid_1_To_Valid (X)));
   end Test_2;

   function R_Invalid_2_To_Valid is new Ada.Unchecked_Conversion (R_Invalid_2, R_Valid);
   function R_Valid_To_Invalid_2 is new Ada.Unchecked_Conversion (R_Valid, R_Invalid_2) with Potentially_Invalid;

   procedure Test_3 (X : R_Valid) is
   begin
      pragma Assert
        (if R_Valid_To_Invalid_2 (X)'Valid_Scalars
         then X = R_Invalid_2_To_Valid (R_Valid_To_Invalid_2 (X)));
      pragma Assert
        (R_Valid_To_Invalid_1 (X)'Valid_Scalars); --  ASSERT:FAIL
   end Test_3;

   procedure Test_4 (X : R_Invalid_2) is
   begin
      pragma Assert
        (R_Valid_To_Invalid_2 (R_Invalid_2_To_Valid (X))'Valid_Scalars);
      pragma Assert
        (X = R_Valid_To_Invalid_2 (R_Invalid_2_To_Valid (X)));
   end Test_4;

   function R_Invalid_1_To_Invalid_2 is new Ada.Unchecked_Conversion (R_Invalid_1, R_Invalid_2) with Potentially_Invalid;
   function R_Invalid_2_To_Invalid_1 is new Ada.Unchecked_Conversion (R_Invalid_2, R_Invalid_1) with Potentially_Invalid;

   procedure Test_5 (X : R_Invalid_1) is
   begin
      pragma Assert
        (if R_Invalid_1_To_Invalid_2 (X)'Valid_Scalars
         then R_Invalid_2_To_Invalid_1 (R_Invalid_1_To_Invalid_2 (X))'Valid_Scalars
             and X = R_Invalid_2_To_Invalid_1 (R_Invalid_1_To_Invalid_2 (X)));
      pragma Assert
        (R_Invalid_1_To_Invalid_2 (X)'Valid_Scalars); --  ASSERT:FAIL
   end Test_5;

   procedure Test_6 (X : R_Invalid_2) is
   begin
      pragma Assert
        (if R_Invalid_2_To_Invalid_1 (X)'Valid_Scalars
         then R_Invalid_1_To_Invalid_2 (R_Invalid_2_To_Invalid_1 (X))'Valid_Scalars
             and X = R_Invalid_1_To_Invalid_2 (R_Invalid_2_To_Invalid_1 (X)));
      pragma Assert
        (R_Invalid_2_To_Invalid_1 (X)'Valid_Scalars); --  ASSERT:FAIL
   end Test_6;

begin
   null;
end Test;
