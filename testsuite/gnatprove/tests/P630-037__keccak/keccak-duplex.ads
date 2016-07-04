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

generic
   -- Size of the Duplex state in bits (e.g. 1600 for Keccak[1600])
   State_Size : Positive;

   -- Type for the Duplex state (e.g. this could be a Keccak[1600] state).
   type State_Type is private;

   -- Procedure to initialize the state.
   with procedure Init_State(A : out State_Type);

   -- Procedure to permute the state.
   with procedure F(A : in out State_Type);

   -- Procedure to XOR bits into the generic state.
   with procedure XOR_Bits_Into_State(A       : in out State_Type;
                                      Data    : in     Keccak.Types.Byte_Array;
                                      Bit_Len : in     Natural);

   -- Procedure to copy bytes from the generic state.
   with procedure Extract_Bits(A       : in     State_Type;
                               Data    :    out Keccak.Types.Byte_Array;
                               Bit_Len : in     Natural);

   -- Procedure to apply the padding rule to a block of bytes.
   with procedure Pad(Block          : in out Keccak.Types.Byte_Array;
                      Num_Used_Bits  : in     Natural;
                      Max_Bit_Length : in     Natural);

   -- The minimum number of bits that are added to the message  by the padding
   -- rule. The duplex constructon ensures that this amount of bits is free
   -- in the block before the padding is applied.
   Min_Padding_Bits : Natural;

   -- @summary
   -- Generic implementation of the Duplex cryptographic construction.
   --
   -- @description
   -- The duplex construction is a cryptographic scheme defined in the
   -- specification "Cryptographic Sponge Functions" from authors of Keccak.
package Keccak.Duplex
is
   subtype Rate_Number is Positive range 1 + Min_Padding_Bits .. State_Size - 1;

   type Context is private;

   procedure Init(Ctx      :    out Context;
                  Capacity : in     Positive)
     with Depends => (Ctx => (Capacity, State_Size)),
     Pre => (Capacity < (State_Size - Min_Padding_Bits)),
     Post => Rate_Of(Ctx) = State_Size - Capacity,
     Global => (Input => State_Size);
   -- Initialize the context.
   --
   -- After initialization, the rate is equal to the State_Size - Capacity.
   -- For example, if the state size is 1600 bits and the capacity is 512 bits
   -- then the rate is 1088 bits.
   --
   -- @param Ctx The context to initialize.
   --
   -- @param Capacity Specifies the capacity (in bits) of the duplex state.
   -- This value must be at least 1, and must leave enough bits free for the
   -- at least 1 data bit & the padding bits to be applied to each block.
   -- For example, if the minmum number of padding is 2 bits, and the state
   -- size is 1600 bits, then the capacity cannot exceed 1597 bits.



   function Rate_Of(Ctx : in Context) return Rate_Number;
   -- Get the rate of the context.
   --
   -- @return The rate (in bits). This is always less than the State_Size


   function Max_Input_Length(Ctx : in Context) return Positive;
   -- Get the maximum number of input bits that can be provided
   -- to duplex invocations.
   --
   -- The maximum number of input bits depends on the rate, and transitively the
   -- capacity which is configured when the context is initialized.
   --
   -- @return The maximum number of input bits that are accepted for
   -- duplex operations.



   procedure Duplex(Ctx                 : in out Context;
                    In_Data             : in     Keccak.Types.Byte_Array;
                    In_Data_Bit_Length  : in     Natural;
                    Out_Data            :    out Keccak.Types.Byte_Array;
                    Out_Data_Bit_Length : in     Natural)
     with Depends => (Ctx      => (Ctx, In_Data, In_Data_Bit_Length),
                      Out_Data => (Ctx, In_Data, In_Data_Bit_Length, Out_Data, Out_Data_Bit_Length)),
     Pre => (In_Data_Bit_Length <= Max_Input_Length(Ctx)
             and then In_Data'Length >= (In_Data_Bit_Length + 7) / 8
             and then Out_Data_Bit_Length <= Rate_Of(Ctx)
             and then Out_Data'Length = (Out_Data_Bit_Length + 7) / 8),
     Post => (Rate_Of(Ctx) = Rate_Of(Ctx'Old));
   -- Run a single duplex block.
   --
   -- @param Ctx The duplex context.
   --
   -- @param In_Data The data to input into the duplex state.
   --
   -- @param In_Data_Bit_Length Specifies the bit-length of the data in the
   -- In_Data array. This length must be smaller than the rate, and must leave
   -- enough space for the padding bits.

   procedure Duplex_Blank(Ctx                 : in out Context;
                          Out_Data            :    out Keccak.Types.Byte_Array;
                          Out_Data_Bit_Length : in     Natural)
     with Depends => (Ctx      => Ctx,
                      Out_Data => (Ctx, Out_Data, Out_Data_Bit_Length)),
     Pre => (Out_Data_Bit_Length <= Rate_Of(Ctx)
             and then Out_Data'Length = (Out_Data_Bit_Length + 7)/8),
     Post => (Rate_Of(Ctx) = Rate_Of(Ctx'Old));
   -- Perform a duplex call without input.
   --
   -- This procedure is equivalent to a call to the Duplex procedure where
   -- the length of the input is 0 bits.
   --
   -- @param Out_Data The output bits from the duplex call are written to
   -- this byte array. If the rate of the duplex object is not a multiple of
   -- 8 bits then any unused bits in the last byte of a complete output block
   -- are set to 0.

   procedure Duplex_Mute(Ctx                : in out Context;
                         In_Data            : in     Keccak.Types.Byte_Array;
                         In_Data_Bit_Length : in     Natural)
     with Depends => (Ctx => + (In_Data, In_Data_Bit_Length)),
     Pre => (In_Data_Bit_Length <= Max_Input_Length(Ctx)
             and then In_Data'Length >= (In_Data_Bit_Length + 7) / 8),
     Post => (Rate_Of(Ctx) = Rate_Of(Ctx'Old));
   -- Perform a duplex call without output.
   --
   -- This procedure is equivalent to a call to the Duplex procedure where
   -- the length of the output is 0 bits (i.e. the output is ignored).
   --
   -- @param In_Data The data to input into the duplex state.
   --
   -- @param In_Data_Bit_Length Specifies the bit-length of the data in the
   -- In_Data array. This length must be smaller than the rate, and must leave
   -- enough space for the padding bits.

private

   type Context is record
      State : State_Type;
      Rate  : Rate_Number;
   end record;

   function Rate_Of(Ctx : in Context) return Rate_Number
   is (Ctx.Rate);

   function Max_Input_Length(Ctx : in Context) return Positive
   is (Rate_Of(Ctx) - Min_Padding_Bits);

end Keccak.Duplex;
