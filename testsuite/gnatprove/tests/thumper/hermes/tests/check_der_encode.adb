---------------------------------------------------------------------------
-- FILE    : check_der_encode.adb
-- SUBJECT : Package containing tests of ASN.1 DER encoding.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit.Assertions;
with Hermes.DER.Encode;

use AUnit.Assertions;
use Hermes;
use Hermes.DER;
use Hermes.DER.Encode;

package body Check_DER_Encode is

   procedure Test_Put_Length(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      type Output_Record is
         record
            Value : Hermes.Octet_Array(1 .. 5);
            Size : Positive;
         end record;

      type Test_Case is
         record
            Input : Natural;
            Expected : Output_Record;
         end record;

      Test_Cases : constant array(1 .. 10) of Test_Case :=
        ( 1 => (Input => 0,
                Expected => (Value => (16#00#, others => 0), Size => 1)),
          2 => (Input => 1,
                Expected => (Value => (16#01#, others => 0), Size => 1)),
          3 => (Input => 127,
                Expected => (Value => (16#7F#, others => 0), Size => 1)),
          4 => (Input => 128,
                Expected => (Value => (16#81#, 16#80#, others => 0), Size => 2)),
          5 => (Input => 255,
                Expected => (Value => (16#81#, 16#FF#, others => 0), Size => 2)),
          6 => (Input => 256,
                Expected => (Value => (16#82#, 16#01#, 16#00#, others => 0), Size => 3)),
          7 => (Input => 16#FFFF#,
                Expected => (Value => (16#82#, 16#FF#, 16#FF#, others => 0), Size => 3)),
          8 => (Input => 16#1_0000#,
                Expected => (Value => (16#83#, 16#01#, 16#00#, 16#00#, others => 0), Size => 4)),
          9 => (Input => 16#FF_0000#,
                Expected => (Value => (16#83#, 16#FF#, 16#00#, 16#00#, others => 0), Size => 4)),
         10 => (Input => 16#7FFF_FFFF#,
                Expected => (Value => (16#84#, 16#7F#, 16#FF#, 16#FF#, 16#FF#), Size => 5)));

   begin
      for I in Test_Cases'Range loop
         declare
            Result : constant Hermes.Octet_Array := Put_Length_Value(Test_Cases(I).Input);
         begin
            Assert
              (Result'Length = Test_Cases(I).Expected.Size,
               "Test case #" & Integer'Image(I) & " length failed");
            Assert
              (Result = Test_Cases(I).Expected.Value(1 .. Test_Cases(I).Expected.Size),
               "Test case #" & Integer'Image(I) & " value failed");
         end;
      end loop;
   end Test_Put_Length;


   procedure Test_Put_Boolean(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      Boolean_False : constant Hermes.Octet_Array := (16#01#, 16#01#, 16#00#);
      Boolean_True  : constant Hermes.Octet_Array := (16#01#, 16#01#, 16#FF#);
   begin
      Assert(Put_Boolean_Value(False) = Boolean_False, "False case failed");
      Assert(Put_Boolean_Value(True) = Boolean_True, "True case failed");
   end Test_Put_Boolean;


   procedure Test_Put_Integer(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      type Output_Record is
         record
            Value : Hermes.Octet_Array(1 .. 6);
            Size : Positive;
         end record;

      type Test_Case is
         record
            Input : Integer;
            Expected : Output_Record;
         end record;

      -- TODO: Add test cases for negative integers.
      Test_Cases : constant array(1 .. 10) of Test_Case :=
        ( 1 => (Input => 0,
                Expected => ((16#02#, 16#01#, 16#00#, others => 0), Size => 3)),
          2 => (Input => 1,
                Expected => ((16#02#, 16#01#, 16#01#, others => 0), Size => 3)),
          3 => (Input => 127,
                Expected => ((16#02#, 16#01#, 16#7F#, others => 0), Size => 3)),
          4 => (Input => 128,
                Expected => ((16#02#, 16#02#, 16#00#, 16#80#, others => 0), Size => 4)),
          5 => (Input => 255,
                Expected => ((16#02#, 16#02#, 16#00#, 16#FF#, others => 0), Size => 4)),
          6 => (Input => 256,
                Expected => ((16#02#, 16#02#, 16#01#, 16#00#, others => 0), Size => 4)),
          7 => (Input => 16#FFFF#,
                Expected => ((16#02#, 16#03#, 16#00#, 16#FF#, 16#FF#, others => 0), Size => 5)),
          8 => (Input => 16#1_0000#,
                Expected => ((16#02#, 16#03#, 16#01#, 16#00#, 16#00#, others => 0), Size => 5)),
          9 => (Input => 16#FF_0000#,
                Expected => ((16#02#, 16#04#, 16#00#, 16#FF#, 16#00#, 16#00#), Size => 6)),
         10 => (Input => 16#7FFF_FFFF#,
                Expected => ((16#02#, 16#04#, 16#7F#, 16#FF#, 16#FF#, 16#FF#), Size => 6)));
   begin
      for I in Test_Cases'Range loop
         declare
            Result : constant Hermes.Octet_Array := Put_Integer_Value(Test_Cases(I).Input);
         begin
            Assert
              (Result'Length = Test_Cases(I).Expected.Size,
               "Test case #" & Integer'Image(I) & " length failed");
            Assert
              (Result = Test_Cases(I).Expected.Value(1 .. Test_Cases(I).Expected.Size),
               "Test case #" & Integer'Image(I) & " value failed");
         end;
      end loop;
   end Test_Put_Integer;


   procedure Register_Tests(T : in out DER_Encode_Test) is
   begin
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Put_Length'Access, "Put Length");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Put_Boolean'Access, "Put Boolean");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Put_Integer'Access, "Put Integer");
   end Register_Tests;


   function Name(T : DER_Encode_Test) return AUnit.Message_String is
      pragma Unreferenced(T);

   begin
      return AUnit.Format("DER.Encode");
   end Name;

end Check_DER_Encode;
