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

with Keccak.Types;

-- @summary
-- Padding rules.
--
-- @description
-- This package contains the implementation of the pad10*1 padding rule.
--
package Keccak.Padding
with SPARK_Mode => On
is

   Pad101_Min_Bits : constant := 2;
   -- The pad10*1 rule appends at least 2 bits

   procedure Pad101_Multi_Blocks(First_Block    : in out Keccak.Types.Byte_Array;
                                 Num_Used_Bits  : in     Natural;
                                 Max_Bit_Length : in     Natural;
                                 Next_Block     :    out Keccak.Types.Byte_Array;
                                 Spilled        :    out Boolean)
     with Depends => (First_Block => + (Num_Used_Bits, Max_Bit_Length),
                      Next_Block  => + (Num_Used_Bits, Max_Bit_Length),
                      Spilled     => (Num_Used_Bits, Max_Bit_Length)),
     Pre => (Next_Block'Length = First_Block'Length
             and then First_Block'Length <= Natural'Last / 8
             and then Max_Bit_Length <= Natural'Last - 7
             and then First_Block'Length = (Max_Bit_Length + 7) / 8
             and then Num_Used_Bits < Max_Bit_Length),
     Post => Spilled = ((Num_Used_Bits + Pad101_Min_Bits) > Max_Bit_Length);
   -- pad10*1 padding rule
   --
   -- This procedure is used in cases where there might not be enough free space
   -- in a block for all the padding bits, in which case the padding spills
   -- over into a second block.
   --
   -- @param First_Block The block which is to be padded. At least 1 padding bit
   --   is applied to this block.
   --
   -- @param Num_Used_Bits The number of bits which are in-use in First_Block.
   --   The padding bits will be applied immediately after this length.
   --
   -- @param Max_Bit_Length The maximum number of bits that can be stored in
   --   First_Block and Next_Block. Padding will only be appended up to this
   --   length.
   --
   -- @param Next_Block If there is less than 2 bits of unused bits in
   --   First_Block then the padding continues into this block. If there
   --   are at least 2 unused bits in First_Block then Next_Block is not used
   --   and is filled with zeroes.
   --
   -- @param Spilled Set to True if there was not enough unused bits in
   --   First_Block to store all of the padding bits. When Spilled is True then
   --   both First_Block and Next_Block contain the padded data.
   --   Otherwise, Spilled is set to False if there is enough free space in
   --   First_Block for all of the padding bits. When Spilled is False then
   --   Next_Block is not used.



   procedure Pad101_Single_Block(Block          : in out Keccak.Types.Byte_Array;
                                 Num_Used_Bits  : in     Natural;
                                 Max_Bit_Length : in     Natural)
     with Depends => (Block => + (Num_Used_Bits, Max_Bit_Length)),
     Pre => (Block'Length <= Natural'Last / 8
             and then Max_Bit_Length <= Natural'Last - 7
             and then Block'Length = (Max_Bit_Length + 7) / 8
             and then Max_Bit_Length >= Pad101_Min_Bits
             and then Num_Used_Bits <= (Max_Bit_Length - Pad101_Min_Bits));
   -- pad10*1 padding rule
   --
   -- This procedure is used in cases where there is always enough space for
   -- the padding bits (at least 2 bits free in the block).
   --
   -- Before calling this function there must be at least 2 bits free in the
   -- block. I.e. Num_Used_Bits <= (Max_Bit_Length - 2).
   --
   -- @param Block The byte array which is to be padded.
   --
   -- @param Num_Used_Bits The number of bits which are currently in-use in the
   --   block. The padding bits are appended after these in-use bits.
   --
   -- @param Max_Bit_Length The maximum bit-size of the block. Padding bits
   -- are applied up to the end of this length.

end Keccak.Padding;
