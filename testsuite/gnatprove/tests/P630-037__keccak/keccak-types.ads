-------------------------------------------------------------------------------
-- Copyright (c) 2016, Daniel King
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * The name of the copyright holder may not be used to endorse or promote
--       Products derived from this software without specific prior written
--       permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
-- ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
-- DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
-- (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
-- LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
-- ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
-- THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- This package defines common types used throughout the various packages
-- in the library.
-------------------------------------------------------------------------------

with Interfaces;

package Keccak.Types
with SPARK_Mode => On
is

   type Unsigned_1 is mod 2**1 with Size => 1;
   type Unsigned_2 is mod 2**2 with Size => 2;
   type Unsigned_4 is mod 2**4 with Size => 4;

   subtype Byte is Interfaces.Unsigned_8;

   subtype Index_Number is Natural;
   type Byte_Array is array(Index_Number range <>) of Byte;


   function Shift_Left_1(Value  : in Unsigned_1;
                         Amount : in Natural) return Unsigned_1
     with Inline,
     Pre => Amount <= 1;

   function Shift_Left_2(Value  : in Unsigned_2;
                         Amount : in Natural) return Unsigned_2
     with Inline,
     Pre => Amount <= 2;

   function Shift_Left_4(Value  : in Unsigned_4;
                         Amount : in Natural) return Unsigned_4
     with Inline,
     Pre => Amount <= 4;


   function Shift_Right_1(Value  : in Unsigned_1;
                          Amount : in Natural) return Unsigned_1
     with Inline,
     Pre => Amount <= 1;

   function Shift_Right_2(Value  : in Unsigned_2;
                          Amount : in Natural) return Unsigned_2
     with Inline,
     Pre => Amount <= 2;

   function Shift_Right_4(Value  : in Unsigned_4;
                          Amount : in Natural) return Unsigned_4
     with Inline,
     Pre => Amount <= 4;


   function Rotate_Left_1(Value  : in Unsigned_1;
                          Amount : in Natural) return Unsigned_1
     with Inline,
     Pre => Amount <= 1;

   function Rotate_Left_2(Value  : in Unsigned_2;
                          Amount : in Natural) return Unsigned_2
     with Inline,
     Pre => Amount <= 2;

   function Rotate_Left_4(Value  : in Unsigned_4;
                          Amount : in Natural) return Unsigned_4
     with Inline,
     Pre => Amount <= 4;

private
   use type Interfaces.Unsigned_8;

   function Shift_Left_1(Value  : in Unsigned_1;
                         Amount : in Natural) return Unsigned_1
   is (Unsigned_1(Interfaces.Shift_Left(Byte(Value), Amount) and (2**1 - 1)));

   function Shift_Left_2(Value  : in Unsigned_2;
                         Amount : in Natural) return Unsigned_2
   is (Unsigned_2(Interfaces.Shift_Left(Byte(Value), Amount) and (2**2 - 1)));

   function Shift_Left_4(Value  : in Unsigned_4;
                         Amount : in Natural) return Unsigned_4
   is (Unsigned_4(Interfaces.Shift_Left(Byte(Value), Amount) and (2**4 - 1)));



   function Shift_Right_1(Value  : in Unsigned_1;
                          Amount : in Natural) return Unsigned_1
   is (Unsigned_1(Interfaces.Shift_Right(Byte(Value), Amount) and (2**1 - 1)));

   function Shift_Right_2(Value  : in Unsigned_2;
                          Amount : in Natural) return Unsigned_2
   is (Unsigned_2(Interfaces.Shift_Right(Byte(Value), Amount) and (2**2 - 1)));

   function Shift_Right_4(Value  : in Unsigned_4;
                          Amount : in Natural) return Unsigned_4
   is (Unsigned_4(Interfaces.Shift_Right(Byte(Value), Amount) and (2**4 - 1)));


   function Rotate_Left_1(Value  : in Unsigned_1;
                          Amount : in Natural) return Unsigned_1
   is (Value);

   function Rotate_Left_2(Value  : in Unsigned_2;
                          Amount : in Natural) return Unsigned_2
   is (Shift_Left_2(Value, Amount) or Shift_Right_2(Value, 2 - Amount));

   function Rotate_Left_4(Value  : in Unsigned_4;
                          Amount : in Natural) return Unsigned_4
   is (Shift_Left_4(Value, Amount) or Shift_Right_4(Value, 4 - Amount));

end Keccak.Types;
