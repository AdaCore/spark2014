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

generic
package Keccak.KeccakF.Byte_Lanes
is

   procedure XOR_Bits_Into_State(A       : in out State;
                                 Data    : in     Keccak.Types.Byte_Array;
                                 Bit_Len : in     Natural)
     with Depends => (A => + (Data, Bit_Len)),
     Pre => (Data'Length <= Natural'Last / 8
             and then Bit_Len <= Data'Length * 8
             and then Bit_Len <= B);
   -- XOR bits into the Keccak-f state.
   --
   -- @param A The Keccak-f state which is XORed with the Data.
   --
   -- @param Data Byte array containing the data to XOR into the state.
   --
   -- @param Bit_Len The number of bits to XOR into the Keccak-f state. This
   --   value cannot be larger than the bit-length of the 'Data' array, and
   --   cannot be larger than the Keccak-f state size.



   procedure Extract_Bytes(A    : in     State;
                           Data :    out Keccak.Types.Byte_Array)
     with Depends => (Data => + A),
     Pre => Data'Length <= ((B + 7)/8);
   -- Extract bytes from the Keccak-f state.
   --
   -- This procedure can be used to read the Keccak-f state, for example: to
   -- read the Keccak-f state after it is permuted.
   --
   -- @param A The Keccak-f state to read.
   --
   -- @param Data The bytes from the Keccak-f state are copied to this buffer.
   --   Note that the buffer can be smaller than the state size if fewer bytes
   --   are needed.

   procedure Extract_Bits(A       : in     State;
                          Data    :    out Keccak.Types.Byte_Array;
                          Bit_Len : in     Natural)
     with Depends => (Data => + (A, Bit_Len)),
     Pre => (Bit_Len <= B
             and then Data'Length = (Bit_Len + 7) / 8);

end Keccak.KeccakF.Byte_Lanes;
