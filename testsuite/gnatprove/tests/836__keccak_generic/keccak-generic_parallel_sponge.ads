-------------------------------------------------------------------------------
--  Copyright (c) 2019, Daniel King
--  All rights reserved.
--
--  Redistribution and use in source and binary forms, with or without
--  modification, are permitted provided that the following conditions are met:
--      * Redistributions of source code must retain the above copyright
--        notice, this list of conditions and the following disclaimer.
--      * Redistributions in binary form must reproduce the above copyright
--        notice, this list of conditions and the following disclaimer in the
--        documentation and/or other materials provided with the distribution.
--      * The name of the copyright holder may not be used to endorse or promote
--        Products derived from this software without specific prior written
--        permission.
--
--  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
--  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
--  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
--  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
--  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
--  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
--  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
--  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
--  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
--  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-------------------------------------------------------------------------------
with Keccak.Types;

--  @summary
--  Generic parallel sponge construction.
--
--  @description
--  This parallel sponge is built on top of a parallel permutation, which
--  can perform multiple separate permutations in parallel by taking
--  advantage of SIMD instructions sets (e.g. SSE2, AVX2).
--
--  @group Sponge
generic
   State_Size : Positive;
   --  Size in bits of the underlying permutation state.
   --  E.g. for Keccak-f[1600] this should be set to 1600.

   type State_Type is private;
   --  Type of the parallel permutation state.

   Parallelism : Positive;
   --  Number of parallel instances provided by State_Type.

   with procedure Init (S : out State_Type);
   --  Initializes the parallel permutation states.

   with procedure Permute_All (S : in out State_Type);
   --  Applies the permutation function to each state in parallel.

   with procedure XOR_Bits_Into_State_Separate
     (S           : in out State_Type;
      Data        : in     Types.Byte_Array;
      Data_Offset : in     Natural;
      Bit_Len     : in     Natural);
   --  XOR bits into a specific instance of the permutation state.

   with procedure XOR_Bits_Into_State_All
     (S           : in out State_Type;
      Data        : in     Types.Byte_Array;
      Bit_Len     : in     Natural);

   with procedure Extract_Bytes (S           : in     State_Type;
                                 Data        :    out Keccak.Types.Byte_Array;
                                 Data_Offset : in     Natural;
                                 Byte_Len    : in     Natural);
   --  Extracts a bytes of output from the state

   with procedure Pad (Block          : in out Keccak.Types.Byte_Array;
                       Num_Used_Bits  : in     Natural;
                       Max_Bit_Length : in     Natural);
   --  Apply the padding rule to a block of data.

   Min_Padding_Bits : Natural;
   --  Minimum number of padding bits appended to the message.
   --
   --  E.g. for pad10*1 there are a minimum of 2 padding bits (two '1' bits).

package Keccak.Generic_Parallel_Sponge
is
   Num_Parallel_Instances : constant Positive := Parallelism;

   Block_Size_Bits        : constant Positive := State_Size;

   subtype Rate_Bits_Number is Positive range 1 .. State_Size - 1
     with Dynamic_Predicate => Rate_Bits_Number mod 8 = 0;
   --  Number representing the Rate (in bits).
   --
   --  The Rate must be a positive integer, and less than the size of the
   --  state (i.e. there must be at least 1 bit of "capacity"). Furthermore,
   --  this implementation restricts the Rate to a multiple of 8 bits.

   type Context (Capacity : Positive) is private;

   type States is (Absorbing, Squeezing, Finished);

   procedure Init (Ctx : out Context)
     with Global => null,
     Pre => (Ctx.Capacity < State_Size
             and then (State_Size - Ctx.Capacity) mod 8 = 0),
     Post => State_Of (Ctx) = Absorbing;
   --  Initialise the sponge.

   function State_Of (Ctx : in Context) return States;
   --  Get the current state of the context.

   function Rate_Of (Ctx : in Context) return Rate_Bits_Number
   is (Block_Size_Bits - Ctx.Capacity);
   --  Get the configured rate parameter (in bits).

private

   subtype Rate_Bytes_Number is Positive range 1 .. ((State_Size + 7) / 8) - 1;
   --  The rate number here represents bytes, not bits.
   --  This makes it easier to handle in proof, since bytes are
   --  always a multiple of 8 bits.

   type Context (Capacity : Positive) is record
      Permutation_State : State_Type;
      Rate              : Rate_Bytes_Number;
      State             : States;
   end record
     with Predicate =>
       (Context.Rate = (State_Size - Context.Capacity) / 8
        and then (State_Size - Context.Capacity) mod 8 = 0
        and then Context.Rate * 8 = State_Size - Context.Capacity);

   function State_Of (Ctx : in Context) return States
   is (Ctx.State);

end Keccak.Generic_Parallel_Sponge;
