package Types with
  SPARK_Mode
is
   --  Same type definitions as in Ada.Interfaces

   type Integer_32 is range -2 ** 31 .. 2 ** 31 - 1;

   type Unsigned_32 is mod 2 ** 32;

   type Unsigned_16 is mod 2 ** 16;

   type Unsigned_8 is mod 2 ** 8;

   --  Same function as in Interfaces

   function Shift_Right (Value : Unsigned_32; Count : Natural) return Unsigned_32
      with Import,
      Convention => Intrinsic,
     Global     => null;

   function Shift_Right (Value : Unsigned_16; Count : Natural) return Unsigned_16
      with Import,
      Convention => Intrinsic,
     Global     => null;

   function Shift_Left (Value : Unsigned_32; Count : Natural) return Unsigned_32
      with Import,
      Convention => Intrinsic,
     Global     => null;

   function Shift_Left (Value : Unsigned_16; Count : Natural) return Unsigned_16
      with Import,
      Convention => Intrinsic,
      Global     => null;

   --  Subtypes of Integer_32

   subtype Natural_32 is Integer_32 range 0 .. 2 ** 31 - 1;

   subtype Positive_32 is Integer_32 range 1 .. 2 ** 31 - 1;

   --  Same as standard floating point type

   type Float_32 is new Float;
   type Float_64 is new Long_Float;

   --  Array of 10 integers

   type Index_10 is range 1 .. 10;

   type Array_10_Integer_32 is array (Index_10) of Integer_32;

   --  Uninterpreted property over integers

   function Property (X : Integer_32; Y : Index_10) return Boolean;

end Types;
