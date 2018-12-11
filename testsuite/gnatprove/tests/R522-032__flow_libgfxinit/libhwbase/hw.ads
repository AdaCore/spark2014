--
-- Copyright (C) 2015-2017 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

with Interfaces;

package HW with Pure is

   type Bit is mod 2 ** 1;

   subtype Byte is Interfaces.Unsigned_8;
   subtype Word8 is Byte;
   function Shift_Left  (Value : Word8; Amount : Natural) return Word8
      renames Interfaces.Shift_Left;
   function Shift_Right (Value : Word8; Amount : Natural) return Word8
      renames Interfaces.Shift_Right;

   subtype Word16 is Interfaces.Unsigned_16;
   function Shift_Left  (Value : Word16; Amount : Natural) return Word16
      renames Interfaces.Shift_Left;
   function Shift_Right (Value : Word16; Amount : Natural) return Word16
      renames Interfaces.Shift_Right;

   subtype Word32 is Interfaces.Unsigned_32;
   function Shift_Left  (Value : Word32; Amount : Natural) return Word32
      renames Interfaces.Shift_Left;
   function Shift_Right (Value : Word32; Amount : Natural) return Word32
      renames Interfaces.Shift_Right;

   subtype Word64 is Interfaces.Unsigned_64;
   function Shift_Left  (Value : Word64; Amount : Natural) return Word64
      renames Interfaces.Shift_Left;
   function Shift_Right (Value : Word64; Amount : Natural) return Word64
      renames Interfaces.Shift_Right;

   subtype Int8 is Interfaces.Integer_8;
   subtype Int16 is Interfaces.Integer_16;
   subtype Int32 is Interfaces.Integer_32;
   subtype Int64 is Interfaces.Integer_64;

   subtype Pos8 is Interfaces.Integer_8 range 1 .. Interfaces.Integer_8'Last;
   subtype Pos16 is Interfaces.Integer_16 range 1 .. Interfaces.Integer_16'Last;
   subtype Pos32 is Interfaces.Integer_32 range 1 .. Interfaces.Integer_32'Last;
   subtype Pos64 is Interfaces.Integer_64 range 1 .. Interfaces.Integer_64'Last;

   use type Pos8;
   function Div_Round_Up (N, M : Pos8) return Pos8 is ((N + (M - 1)) / M)
   with
      Pre => N <= Pos8'Last - (M - 1);
   function Div_Round_Closest (N, M : Pos8) return Int8 is ((N + M / 2) / M)
   with
      Pre => N <= Pos8'Last - M / 2;

   use type Pos16;
   function Div_Round_Up (N, M : Pos16) return Pos16 is ((N + (M - 1)) / M)
   with
      Pre => N <= Pos16'Last - (M - 1);
   function Div_Round_Closest (N, M : Pos16) return Int16 is ((N + M / 2) / M)
   with
      Pre => N <= Pos16'Last - M / 2;

   use type Pos32;
   function Div_Round_Up (N, M : Pos32) return Pos32 is ((N + (M - 1)) / M)
   with
      Pre => N <= Pos32'Last - (M - 1);
   function Div_Round_Closest (N, M : Pos32) return Int32 is ((N + M / 2) / M)
   with
      Pre => N <= Pos32'Last - M / 2;

   use type Pos64;
   function Div_Round_Up (N, M : Pos64) return Pos64 is ((N + (M - 1)) / M)
   with
      Pre => N <= Pos64'Last - (M - 1);
   function Div_Round_Closest (N, M : Pos64) return Int64 is ((N + M / 2) / M)
   with
      Pre => N <= Pos64'Last - M / 2;

   subtype Buffer_Range is Natural range 0 .. Natural'Last - 1;
   type Buffer is array (Buffer_Range range <>) of Byte;

end HW;
