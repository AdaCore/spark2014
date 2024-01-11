with Ada.Unchecked_Conversion;
with System;

procedure Imprecise is

   type U8 is mod 2**8;
   type U16 is mod 2**16;
   type U32 is mod 2**32;
   type U64 is mod 2**64;
   type U128 is mod 2**128;

   function UC1 is new Ada.Unchecked_Conversion (Source => U32, Target => U16);

   type R2 is record
      A : U32;
   end record;

   function UC2 is new Ada.Unchecked_Conversion (Source => U32, Target => R2);

   type R3 is record
      A : Character;
   end record;
   for R3 use record
      A at 0 range 0 .. 7;
   end record;

   function UC3 is new Ada.Unchecked_Conversion (Source => U8, Target => R3);

   type R4 is record
      A : U32;
   end record with Scalar_Storage_Order => System.High_Order_First,
                   Bit_Order => System.High_Order_First;
   for R4 use record
      A at 0 range 0 .. 31;
   end record;

   function UC4 is new Ada.Unchecked_Conversion (Source => U32, Target => R4);

   type Biased is range -1 .. 2**16-2 with Size => 16;
   type R5 is record
      A : Biased;
   end record;
   for R5 use record
      A at 0 range 0 .. 15;
   end record;

   function UC5 is new Ada.Unchecked_Conversion (Source => U16, Target => R5);

   type R6 (X : Integer) is record
      A : U32;
   end record;
   for R6 use record
      X at 0 range 0 .. 31;
      A at 0 range 32 .. 63;
   end record;

   function UC6 is new Ada.Unchecked_Conversion (Source => U64, Target => R6);

   type R7 is tagged record
      A : U64;
   end record;
   for R7 use record
      A at 0 range 64 .. 127;
   end record;

   function UC7 is new Ada.Unchecked_Conversion (Source => U128, Target => R7);

   -----

   type A1 is array (1..2, 1..2) of U8 with Size => 32;

   function AUC1 is new Ada.Unchecked_Conversion (Source => A1, Target => U32);

   type A2 is array (1..2) of U16 with
     Size => 32,
     Scalar_Storage_Order => System.High_Order_First;

   function AUC2 is new Ada.Unchecked_Conversion (Source => A2, Target => U32);

   type A3 is array (1..2) of Float with
     Size => 64;

   function AUC4 is new Ada.Unchecked_Conversion (Source => U64, Target => A3);

   type A4 is array (1..2) of Character with
     Size => 16;

   function AUC4 is new Ada.Unchecked_Conversion (Source => U16, Target => A4);

   -----

   package P is
      type P32 is private;

   private
      type P32 is new Positive;
      function PUC1 is new Ada.Unchecked_Conversion (Source => U32, Target => P32);
   end P;

   function PUC1 is new Ada.Unchecked_Conversion (Source => U32, Target => P.P32);

begin
   null;
end;
