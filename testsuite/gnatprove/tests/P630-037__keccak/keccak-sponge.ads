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
   -- Size of the Sponge state in bits (e.g. 1600 for Keccak[1600])
   State_Size : Positive;

   -- Type for the internal state.
   type State_Type is private;

   -- Procedure to initialize the state
   with procedure Init_State(A : out State_Type);

   -- Procedure to permute the state
   with procedure F(A : in out State_Type);

   -- Procedure to XOR bits into the internal state.
   with procedure XOR_Bits_Into_State(A       : in out State_Type;
                                      Data    : in     Keccak.Types.Byte_Array;
                                      Bit_Len : in Natural);

   -- Extracts a block of output from the state
   with procedure Extract_Data(A     : in     State_Type;
                               Data  :    out Keccak.Types.Byte_Array);

   -- Padding rule
   with procedure Pad(First_Block    : in out Keccak.Types.Byte_Array;
                      Num_Used_Bits  : in     Natural;
                      Max_Bit_Length : in     Natural;
                      Next_Block     :    out Keccak.Types.Byte_Array;
                      Spilled        :    out Boolean);

   -- @summary
   -- This package implements the sponge construction.
   --
   -- @description
   -- The sponge construction is defined in Section 2.2 of "Cryptographic Sponge
   -- Functions" (see also Section 4 of NIST FIPS 202).
   --
   -- This package is generic and can be used with any fixed-length transformation
   -- permutation (such as Keccak). The following formal generics are required to
   -- define the state, and the operations on the state which are required by the
   -- sponge:
   -- * The type of the state is defined by the 'State' parameter.
   -- * The bit-length of the state is defined by the 'State_Size' parameter.
   -- * The 'Init_State' procedure initializes the state to zeroes.
   -- * The 'XOR_Bits_Into_State' procedure XORs bits into the state.
   -- * The 'F' procedure permutes the state.
   -- * The 'Extract_Data' procedure converts all or part of the state into a byte
   --   array.
   --
   -- Additionally, the 'Pad' procedure provides the padding rule, which adds
   -- padding bits into a block of data (the padding may spill over into another
   -- block if there is not enough free bits in the first provided block).
package Keccak.Sponge
is

   type States is (Absorbing, Squeezing);

   type Context is private;

   ----------------------------------------------------------------------------
   -- Sponge procedures
   ----------------------------------------------------------------------------

   procedure Init(Ctx             :    out Context;
                  Capacity        : in     Positive)
     with Depends => (Ctx => Capacity),
     Pre => (((State_Size - Capacity) mod 8 = 0) and (Capacity < State_Size)),
     Post => ((State_Of(Ctx) = Absorbing)
              and (Rate_Of(Ctx) = State_Size - Capacity)
              and In_Queue_Bit_Length(Ctx) = 0),
     Global => null;
   -- Initialize the context with the specified capacity.
   --
   -- The following example demonstrates initializing a sponge with a capacity
   -- of 512 bits:
   --     Init(Ctx, 512);
   --
   -- After initialization, the sponge is in the Absorbing state. Bits are
   -- absorbed into the sponge using the Absorb procedure. Alternatively, it
   -- is possible to immediately squeeze data from the sponge using the Squeeze
   -- procedure, without first absorbing any data into the sponge.
   --
   -- @param Ctx The sponge context to initialize.
   --
   -- @param Capacity The sponge's capacity (in bits). The capacity has the
   --   following requirements:
   --   * Must be positive
   --   * Must be strictly smaller than the State_Size
   --   * Must be a multiple of 8 (this is a requirement for this implementation)


   function State_Of(Ctx : in Context) return States;
   -- Gets the current state of the sponge.
   --
   -- The sponge has two states: Absorbing and Squeezing. Initially the sponge
   -- in the Absorbing state, where bits can be absorbed into the sponge using
   -- the Absorb procedure. The sponge can move into the Squeezing state at
   -- any time by calling the Squeeze procedure.
   --
   -- Once in the Squeezing state the sponge cannot move back into the Absorbing
   -- state. However, the same sponge context can be re-used for a different
   -- computation by re-initializing the sponge.
   --
   -- @return The current state of the sponge.



   function Rate_Of(Ctx : in Context) return Positive
     with Post => Rate_Of'Result < State_Size;
   -- Gets the currently configured rate of the sponge.
   --
   -- The rate is derived from the sponge's capacity and the State_Size.
   --
   -- @return The sponge's rate, in bits.



   procedure Absorb(Ctx        : in out Context;
                    Data       : in     Keccak.Types.Byte_Array;
                    Bit_Length : in     Natural)
     with Depends => (Ctx => + (Data, Bit_Length)),
     Pre => (State_Of(Ctx) = Absorbing
             and then Bit_Length <= Natural'Last - 7
             and then (Bit_Length + 7) / 8 <= Data'Length
             and then In_Queue_Bit_Length(Ctx) mod 8 = 0
             and then In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)),
     Post => (State_Of(Ctx) = Absorbing
              and Rate_Of(Ctx) = Rate_Of(Ctx'Old)
              and (In_Queue_Bit_Length(Ctx) mod 8) = (Bit_Length mod 8)
              and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx));
   -- Absorb (input) bits into the sponge.
   --
   -- This procedure can be called multiple times to absorb large amounts of
   -- data in chunks.
   --
   -- @param Ctx The sponge context to where the data will be absorbed.
   --
   -- @param Data Contains the data to absorb into the sponge.
   --
   -- @param Bit_Length The number of bits from the 'Data' array to absorb
   --   into the sponge. The length of the 'Data' array must contain at least
   --   this many bits. E.g. if Bit_Length is 20 then Data'Length must be at
   --   least 3 bytes.



   procedure Absorb_With_Suffix(Ctx        : in out Context;
                                Message    : in     Keccak.Types.Byte_Array;
                                Bit_Length : in     Natural;
                                Suffix     : in     Keccak.Types.Byte;
                                Suffix_Len : in     Natural)
     with Pre => (State_Of(Ctx) = Absorbing
                  and then Suffix_Len <= 8
                  and then Bit_Length <= Natural'Last - 8
                  and then (Bit_Length + 7) / 8 <= Message'Length
                  and then In_Queue_Bit_Length(Ctx) mod 8 = 0
                  and then In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)),
     Post => (State_Of(Ctx) = Absorbing
              and Rate_Of(Ctx) = Rate_Of(Ctx'Old)
              and (In_Queue_Bit_Length(Ctx) mod 8) = ((Bit_Length + Suffix_Len) mod 8)
              and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx));
   -- Concatenate up to 8 suffix bits to a message, then absorb the resulting
   -- concatenated data into the sponge.
   --
   -- Typically this procedure is called before the first call to Squeeze in
   -- cases where there are additional bits to be appended before the padding.
   -- One example is SHA3, which appends the bits 11 to each message before
   -- the padding bits are appended. An example of using this procedure to
   -- absorb the final data into the sponge is shown below:
   --     Absorb_With_Suffix(Ctx,
   --                        Message,
   --                        Message'Length * 8, -- bit length of the message
   --                        2#11#,              -- Concatenate the bits 11 onto the message
   --                        2);                 -- The suffix is two bits in length
   --
   -- In pseudo-code, this procedure is functionally equivalent to:
   --     Absorb(Ctx, Message || 11);
   --
   -- @param Ctx The sponge context into which the bits will be absorbed.
   --
   -- @param Message Byte array containing the data to absorb.
   --
   -- @param Bit_Length The number of bits in 'Message' to absorb into the sponge.
   --
   -- @param Suffix A byte containing the suffix bits to append to the message.
   --   The least significant bit in this byte is the first bit that is appended.
   --
   -- @param Suffix_Len The number of bits from the 'Suffix' byte to append.
   --   Up to 8 additional bits can be absorbed, and Suffix_Len can be set to 0
   --   if no additional bits should be absorbed.



   procedure Squeeze(Ctx    : in out Context;
                     Digest :    out Keccak.Types.Byte_Array)
     with Depends => ((Ctx, Digest) => (Ctx, Digest)),
     Post => (State_Of(Ctx) = Squeezing
              and Rate_Of(Ctx) = Rate_Of(Ctx'Old));
   -- Squeeze (output) bits from the sponge.
   --
   -- Squeeze can be called multiple times to extract an arbitrary amount of
   -- output bytes.
   --
   -- Note that after calling Squeeze it is not possible to absorb any more
   -- data into the sponge.
   --
   -- @param Ctx The context from where the data will be squeezed.
   --
   -- @param Digest This array is filled with bytes squeezed from the sponge.
   --   This array can be of any length.



   function In_Queue_Bit_Length(Ctx : in Context) return Natural
     with Post => In_Queue_Bit_Length'Result < State_Size;
   -- Get the number of bits which are waiting in the input queue, and have
   -- not yet been absorbed into the sponge.
   --
   -- The purpose of this function is to aid in the definition of the
   -- preconditions and postconditions

private

   -- The rate number here represents bytes, not bits.
   -- This makes it easier to handle in proof, since bytes are
   -- always a multiple of 8 bits.
   subtype Rate_Number is Positive range 1 .. ((State_Size + 7)/8) - 1;

   subtype Byte_Absorption_Number is Natural range 0 .. ((State_Size + 7)/8) - 1;

   subtype Bit_Absorption_Number  is Natural range 0 .. State_Size - 1;

   subtype Block_Type is Keccak.Types.Byte_Array(Byte_Absorption_Number);

   subtype Suffix_Bits_Number is Natural range 0 .. 8;

   type Context is record
      -- The sponge state.
      State           : State_Type;

      -- Input/output queue.
      --
      -- When absorbing, this buffer holds data which is waiting to be absorbed.
      -- When squeezing, this buffer holds squeezed bytes which are waiting to
      -- be read by calling Squeeze.
      Block           : Block_Type;

      -- While absorbing, this keeps track of the number of bits in the input
      -- queue that are waiting to be absorbed.
      Bits_Absorbed   : Bit_Absorption_Number;

      -- While squeezing, this keeps track of the number of bytes
      -- that have been extracted from output queue. Once this value reaches
      -- the rate, then the next block of output is generated and Bytes_Squeezed
      -- is reset to 0.
      Bytes_Squeezed  : Byte_Absorption_Number;

      -- The rate parameter. This value is represented in bytes, not bits
      -- so that it is easier to manage in proof.
      Rate            : Rate_Number;

      -- The current state of the sponge (Absorbing or Squeezing).
      Curr_State      : States;
   end record;

   ----------------------------------------------------------------------------
   -- Sponge Expression functions
   ----------------------------------------------------------------------------

   function State_Of(Ctx : in Context) return States
   is (Ctx.Curr_State);

   function Rate_Of(Ctx : in Context) return Positive
   is (Positive(Ctx.Rate) * 8);

   function In_Queue_Bit_Length(Ctx : in Context) return Natural
   is (Ctx.Bits_Absorbed);

end Keccak.Sponge;
