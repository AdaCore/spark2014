---------------------------------------------------------------------------
-- FILE    : check_der_decode.adb
-- SUBJECT : Package containing tests of ASN.1 DER decoding.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with AUnit.Assertions;
with Hermes.DER.Decode;

use AUnit.Assertions;
use Hermes;
use Hermes.DER;
use Hermes.DER.Decode;

package body Check_DER_Decode is

   type Octet_Array_Access is access Octet_Array;

   procedure Test_Get_Length(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      type Input_Record is
         record
            Data  : Octet_Array_Access;
            Start : Natural;
         end record;

      type Output_Record is
         record
            Stop   : Natural;
            Length : Natural;
            Status : Status_Type;
         end record;

      type Test_Case is
         record
            Input    : Input_Record;
            Expected : Output_Record;
         end record;

      subtype Array_1_Type is Octet_Array(1 .. 1);
      subtype Array_2_Type is Octet_Array(1 .. 2);
      subtype Array_3_Type is Octet_Array(1 .. 3);
      subtype Array_4_Type is Octet_Array(1 .. 4);
      subtype Array_5_Type is Octet_Array(1 .. 5);
      subtype Array_6_Type is Octet_Array(1 .. 6);

      Test_Cases : constant array(1 .. 16) of Test_Case :=
        -- Correctly formatted definite form using the short encoding.
        ( 1 => (Input    => (Data => new Array_1_Type'(1 => 2#0000_0000#), Start => 1),
                Expected => (Stop => 1, Length => 0, Status => Success)),
          2 => (Input    => (Data => new Array_1_Type'(1 => 2#0000_0001#), Start => 1),
                Expected => (Stop => 1, Length => 1, Status => Success)),
          3 => (Input    => (Data => new Array_1_Type'(1 => 2#0111_1111#), Start => 1),
                Expected => (Stop => 1, Length => 127, Status => Success)),

          -- Indefinite length.
          4 => (Input    => (Data => new Array_1_Type'(1 => 2#1000_0000#), Start => 1),
                Expected => (Stop => 1, Length => 0, Status => Indefinite_Length)),

          -- Reserved encoding.
          5 => (Input    => (Data => new Array_1_Type'(1 => 2#1111_1111#), Start => 1),
                Expected => (Stop => 1, Length => 0, Status => Bad_Length)),

          -- Correctly formatted definite form using the long encoding.
          6 => (Input    => (Data => new Array_2_Type'(2#1000_0001#, 0), Start => 1),
                Expected => (Stop => 2, Length => 0, Status => Success)),
          7 => (Input    => (Data => new Array_2_Type'(2#1000_0001#, 1), Start => 1),
                Expected => (Stop => 2, Length => 1, Status => Success)),
          8 => (Input    => (Data => new Array_2_Type'(2#1000_0001#, 255), Start => 1),
                Expected => (Stop => 2, Length => 255, Status => Success)),
          9 => (Input    => (Data => new Array_3_Type'(2#1000_0010#, 0, 1), Start => 1),
                Expected => (Stop => 3, Length => 1, Status => Success)),
         10 => (Input    => (Data => new Array_3_Type'(2#1000_0010#, 1, 0), Start => 1),
                Expected => (Stop => 3, Length => 256, Status => Success)),
         11 => (Input    => (Data => new Array_3_Type'(2#1000_0010#, 255, 255), Start => 1),
                Expected => (Stop => 3, Length => 2**16 - 1, Status => Success)),
         12 => (Input    => (Data => new Array_4_Type'(2#1000_0011#, 255, 255, 255), Start => 1),
                Expected => (Stop => 4, Length => 2**24 - 1, Status => Success)),
         13 => (Input    => (Data => new Array_5_Type'(2#1000_0100#, 127, 255, 255, 255), Start => 1),
                Expected => (Stop => 5, Length => 2**31 - 1, Status => Success)),

         -- Unimplemented lengths.
         14 => (Input    => (Data => new Array_5_Type'(2#1000_0100#, 128, 0, 0, 0), Start => 1),
                Expected => (Stop => 5, Length => 0, Status => Unimplemented_Length)),
               -- Strictly, this next case should work.
         15 => (Input    => (Data => new Array_6_Type'(2#1000_0101#, 0, 0, 0, 0, 1), Start => 1),
                Expected => (Stop => 6, Length => 0, Status => Unimplemented_Length)),

         -- Various error cases.
         16 => (Input    => (Data => new Array_5_Type'(2#1000_0101#, 0, 0, 0, 0), Start => 1),
                Expected => (Stop => 5, Length => 0, Status => Bad_Length)));

      Test_Stop   : Natural;
      Test_Length : Natural;
      Test_Status : Status_Type;
   begin
      for I in Test_Cases'Range loop
         Get_Length_Value
           (Test_Cases(I).Input.Data.all,
            Test_Cases(I).Input.Start,
            Test_Stop,
            Test_Length,
            Test_Status);

         Assert
           (Test_Stop   = Test_Cases(I).Expected.Stop   and
            Test_Length = Test_Cases(I).Expected.Length and
            Test_Status = Test_Cases(I).Expected.Status,
            "Test case #" & Integer'Image(I) & " failed");
      end loop;
   end Test_Get_Length;


   procedure Test_Get_Boolean(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      type Input_Record is
         record
            Data  : Octet_Array_Access;
            Start : Natural;
         end record;
      type Output_Record is
         record
            Stop   : Natural;
            Value  : Boolean;
            Status : Status_Type;
         end record;

      type Test_Case is
         record
            Input    : Input_Record;
            Expected : Output_Record;
         end record;

      subtype Array_3_Type is Octet_Array(1 .. 3);

      Test_Cases : constant array(1 .. 3) of Test_Case :=
        -- Correctly formatted Boolean encodings.
        ( 1 => (Input    => (Data => new Array_3_Type'(16#01#, 16#01#, 16#00#), Start => 1),
                Expected => (Stop => 3, Value => False, Status => Success)),
          2 => (Input    => (Data => new Array_3_Type'(16#01#, 16#01#, 16#FF#), Start => 1),
                Expected => (Stop => 3, Value => True, Status => Success)),

          -- Check an invalid encoding.
          3 => (Input    => (Data => new Array_3_Type'(16#01#, 16#01#, 16#01#), Start => 1),
                Expected => (Stop => 3, Value => False, Status => Bad_Value)));

      Test_Stop   : Natural;
      Test_Value  : Boolean;
      Test_Status : Status_Type;
   begin
      for I in Test_Cases'Range loop
         Get_Boolean_Value
           (Test_Cases(I).Input.Data.all,
            Test_Cases(I).Input.Start,
            Test_Stop,
            Test_Value,
            Test_Status);

         Assert
           (Test_Value  = Test_Cases(I).Expected.Value  and
            Test_Stop   = Test_Cases(I).Expected.Stop   and
            Test_Status = Test_Cases(I).Expected.Status,
            "Test case #" & Integer'Image(I) & " failed");
      end loop;
   end Test_Get_Boolean;


   procedure Test_Get_Integer(T : in out AUnit.Test_Cases.Test_Case'Class) is
      pragma Unreferenced(T);

      type Input_Record is
         record
            Data  : Octet_Array_Access;
            Start : Natural;
         end record;

      type Output_Record is
         record
            Stop   : Natural;
            Value  : Integer;
            Status : Status_Type;
         end record;

      type Test_Case is
         record
            Input    : Input_Record;
            Expected : Output_Record;
         end record;

      subtype Array_3_Type is Octet_Array(1 .. 3);
      subtype Array_4_Type is Octet_Array(1 .. 4);
      subtype Array_6_Type is Octet_Array(1 .. 6);
      subtype Array_7_Type is Octet_Array(1 .. 7);

      Test_Cases : constant array(1 .. 18) of Test_Case :=
        -- Correctly formatted integer encodings.
        ( 1 => (Input    => (Data => new Array_3_Type'(16#02#, 16#01#, 16#00#), Start => 1),
                Expected => (Stop => 3, Value => 0, Status => Success)),
          2 => (Input    => (Data => new Array_3_Type'(16#02#, 16#01#, 16#01#), Start => 1),
                Expected => (Stop => 3, Value => 1, Status => Success)),
          3 => (Input    => (Data => new Array_3_Type'(16#02#, 16#01#, 16#7F#), Start => 1),
                Expected => (Stop => 3, Value => 127, Status => Success)),
          4 => (Input    => (Data => new Array_3_Type'(16#02#, 16#01#, 16#FF#), Start => 1),
                Expected => (Stop => 3, Value => -1, Status => Success)),
          5 => (Input    => (Data => new Array_4_Type'(16#02#, 16#02#, 16#00#, 16#FF#), Start => 1),
                Expected => (Stop => 4, Value => 255, Status => Success)),
          6 => (Input    => (Data => new Array_4_Type'(16#02#, 16#02#, 16#01#, 16#00#), Start => 1),
                Expected => (Stop => 4, Value => 256, Status => Success)),
          7 => (Input    => (Data => new Array_4_Type'(16#02#, 16#02#, 16#01#, 16#FF#), Start => 1),
                Expected => (Stop => 4, Value => 511, Status => Success)),
          8 => (Input    => (Data => new Array_6_Type'(16#02#, 16#04#, 16#7F#, 16#FF#, 16#FF#, 16#FF#), Start => 1),
                Expected => (Stop => 6, Value => 2**31 - 1, Status => Success)),
          9 => (Input    => (Data => new Array_6_Type'(16#02#, 16#04#, 16#80#, 16#00#, 16#00#, 16#00#), Start => 1),
                Expected => (Stop => 6, Value => -2**31, Status => Success)),

         -- Check a few invalid encodings.
         10 => (Input    => (Data => new Array_3_Type'(16#22#, 16#01#, 16#01#), Start => 1),
                Expected => (Stop => 1, Value => 0, Status => Bad_Value)),
         11 => (Input    => (Data => new Array_3_Type'(16#42#, 16#01#, 16#01#), Start => 1),
                Expected => (Stop => 1, Value => 0, Status => Bad_Value)),
         12 => (Input    => (Data => new Array_3_Type'(16#1F#, 16#01#, 16#01#), Start => 1),
                Expected => (Stop => 1, Value => 0, Status => Bad_Value)),
         13 => (Input    => (Data => new Array_3_Type'(16#02#, 16#02#, 16#01#), Start => 1),
                Expected => (Stop => 3, Value => 0, Status => Bad_Value)),
         14 => (Input    => (Data => new Array_4_Type'(16#02#, 16#02#, 16#00#, 16#01#), Start => 1),
                Expected => (Stop => 4, Value => 0, Status => Bad_Value)),
         15 => (Input    => (Data => new Array_4_Type'(16#02#, 16#02#, 16#FF#, 16#80#), Start => 1),
                Expected => (Stop => 4, Value => 0, Status => Bad_Value)),
         16 => (Input    => (Data => new Array_6_Type'(16#02#, 16#04#, 16#FF#, 16#FF#, 16#FF#, 16#FF#), Start => 1),
                Expected => (Stop => 6, Value => 0, Status => Bad_Value)),

         -- Check some unimplemented values.
         17 => (Input    => (Data => new Array_7_Type'(16#02#, 16#05#, 16#00#, 16#80#, 16#00#, 16#00#, 16#00#), Start => 1),
                Expected => (Stop => 7, Value => 0, Status => Unimplemented_Value)),
         18 => (Input    => (Data => new Array_7_Type'(16#02#, 16#05#, 16#FF#, 16#7F#, 16#FF#, 16#FF#, 16#FF#), Start => 1),
                Expected => (Stop => 7, Value => 0, Status => Unimplemented_Value)));

      Test_Stop   : Natural;
      Test_Value  : Integer;
      Test_Status : Status_Type;
   begin
      for I in Test_Cases'Range loop
         Get_Integer_Value
           (Test_Cases(I).Input.Data.all,
            Test_Cases(I).Input.Start,
            Test_Stop,
            Test_Value,
            Test_Status);

         Assert
           (Test_Stop   = Test_Cases(I).Expected.Stop   and
            Test_Value  = Test_Cases(I).Expected.Value  and
            Test_Status = Test_Cases(I).Expected.Status,
            "Test case #" & Integer'Image(I) & " failed");
      end loop;
   end Test_Get_Integer;


   procedure Register_Tests(T : in out DER_Decode_Test) is
   begin
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Get_Length'Access, "Get Length");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Get_Boolean'Access, "Get Boolean");
      AUnit.Test_Cases.Registration.Register_Routine(T, Test_Get_Integer'Access, "Get Integer");
   end Register_Tests;


   function Name(T : DER_Decode_Test) return AUnit.Message_String is
      pragma Unreferenced(T);
   begin
      return AUnit.Format("DER.Decode");
   end Name;

end Check_DER_Decode;
