-------------------------------------------------------------------------------
--  Copyright (c) 2016 Daniel King
--
--  Permission is hereby granted, free of charge, to any person obtaining a
--  copy of this software and associated documentation files (the "Software"),
--  to deal in the Software without restriction, including without limitation
--  the rights to use, copy, modify, merge, publish, distribute, sublicense,
--  and/or sell copies of the Software, and to permit persons to whom the
--  Software is furnished to do so, subject to the following conditions:
--
--  The above copyright notice and this permission notice shall be included in
--  all copies or substantial portions of the Software.
--
--  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
--  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
--  DEALINGS IN THE SOFTWARE.
-------------------------------------------------------------------------------

with Interfaces;

package DW1000.Types
  with SPARK_Mode => On
is
   type Bits_1 is mod 2**1 with Size => 1;
   type Bits_2 is mod 2**2 with Size => 2;
   type Bits_3 is mod 2**3 with Size => 3;
   type Bits_4 is mod 2**4 with Size => 4;
   type Bits_5 is mod 2**5 with Size => 5;
   type Bits_6 is mod 2**6 with Size => 6;
   type Bits_7 is mod 2**7 with Size => 7;

   subtype Bits_8 is Interfaces.Unsigned_8;

   type Bits_9  is mod 2**9  with Size => 9;
   type Bits_10 is mod 2**10 with Size => 10;
   type Bits_11 is mod 2**11 with Size => 11;
   type Bits_12 is mod 2**12 with Size => 12;
   type Bits_13 is mod 2**13 with Size => 13;
   type Bits_14 is mod 2**14 with Size => 14;
   type Bits_15 is mod 2**15 with Size => 15;

   subtype Bits_16 is Interfaces.Unsigned_16;

   type Bits_17 is mod 2**17 with Size => 17;
   type Bits_18 is mod 2**18 with Size => 18;
   type Bits_19 is mod 2**19 with Size => 19;
   type Bits_20 is mod 2**20 with Size => 20;
   type Bits_21 is mod 2**21 with Size => 21;
   type Bits_22 is mod 2**22 with Size => 22;
   type Bits_23 is mod 2**23 with Size => 23;
   type Bits_24 is mod 2**24 with Size => 24;
   type Bits_25 is mod 2**25 with Size => 25;
   type Bits_26 is mod 2**26 with Size => 26;
   type Bits_27 is mod 2**27 with Size => 27;
   type Bits_28 is mod 2**28 with Size => 28;
   type Bits_29 is mod 2**29 with Size => 29;
   type Bits_30 is mod 2**30 with Size => 30;
   type Bits_31 is mod 2**31 with Size => 31;

   subtype Bits_32 is Interfaces.Unsigned_32;

   type Bits_33 is mod 2**33 with Size => 33;
   type Bits_34 is mod 2**34 with Size => 34;
   type Bits_35 is mod 2**35 with Size => 35;
   type Bits_36 is mod 2**36 with Size => 36;
   type Bits_37 is mod 2**37 with Size => 37;
   type Bits_38 is mod 2**38 with Size => 38;
   type Bits_39 is mod 2**39 with Size => 39;
   type Bits_40 is mod 2**40 with Size => 40;
   type Bits_41 is mod 2**41 with Size => 41;
   type Bits_42 is mod 2**42 with Size => 42;
   type Bits_43 is mod 2**43 with Size => 43;
   type Bits_44 is mod 2**44 with Size => 44;
   type Bits_45 is mod 2**45 with Size => 45;
   type Bits_46 is mod 2**46 with Size => 46;
   type Bits_47 is mod 2**47 with Size => 47;
   type Bits_48 is mod 2**48 with Size => 48;
   type Bits_49 is mod 2**49 with Size => 49;
   type Bits_50 is mod 2**50 with Size => 50;
   type Bits_51 is mod 2**51 with Size => 51;
   type Bits_52 is mod 2**52 with Size => 52;
   type Bits_53 is mod 2**53 with Size => 53;
   type Bits_54 is mod 2**54 with Size => 54;
   type Bits_55 is mod 2**55 with Size => 55;
   type Bits_56 is mod 2**56 with Size => 56;
   type Bits_57 is mod 2**57 with Size => 57;
   type Bits_58 is mod 2**58 with Size => 58;
   type Bits_59 is mod 2**59 with Size => 59;
   type Bits_60 is mod 2**60 with Size => 60;
   type Bits_61 is mod 2**61 with Size => 61;
   type Bits_62 is mod 2**62 with Size => 62;
   type Bits_63 is mod 2**63 with Size => 63;

   subtype Bits_64 is Interfaces.Unsigned_64;

   type Byte_Array is array (Natural range <>) of Bits_8;
end DW1000.Types;
