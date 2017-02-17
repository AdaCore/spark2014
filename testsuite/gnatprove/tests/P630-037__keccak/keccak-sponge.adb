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

with Interfaces; use Interfaces;

package body Keccak.Sponge
is

   procedure Init(Ctx      :    out Context;
                  Capacity : in     Positive)
   is
   begin
      Init_State(Ctx.State);

      Ctx.Block           := (others => 0);
      Ctx.Bits_Absorbed   := 0;
      Ctx.Bytes_Squeezed  := 0;
      Ctx.Rate            := (State_Size - Natural(Capacity))/8;
      Ctx.Curr_State      := Absorbing;
   end Init;



   procedure Absorb(Ctx        : in out Context;
                    Data       : in     Keccak.Types.Byte_Array;
                    Bit_Length : in     Natural)
   is
      Offset              : Natural := 0;
      Remaining_Bits      : Natural := Bit_Length;
      Remaining_Bytes     : Natural := (Bit_Length + 7) / 8;
      Initial_Data_Len    : Natural := Remaining_Bytes;

      Free_Bytes_In_Block : Natural;
      Free_Bits_In_Block  : Natural;
      Block_Offset        : Natural;

      Data_Last           : Keccak.Types.Index_Number;

      Initial_Bit_Rate    : Positive := Rate_Of(Ctx);

   begin
      if Initial_Data_Len > 0 then
         Data_Last := Data'First + (Initial_Data_Len - 1);

         -- Calculate how many bits are free in the 'in' queue.
         Free_Bits_In_Block  := Rate_Of(Ctx) - Ctx.Bits_Absorbed;
         Free_Bytes_In_Block := Free_Bits_In_Block / 8;

         pragma Assert(Free_Bits_In_Block < State_Size);
         pragma Assert(Free_Bits_In_Block mod 8 = 0);

         if Bit_Length < Free_Bits_In_Block then
            -- We don't have a complete block, so just store the message
            -- with the other leftovers.
            Block_Offset := Ctx.Bits_Absorbed / 8;
            Ctx.Block(Block_Offset ..
                      (Block_Offset + Remaining_Bytes) - 1) := Data(Data'First .. Data_Last);

            Ctx.Bits_Absorbed := Ctx.Bits_Absorbed + Bit_Length;

         else
            -- Append the first data to any leftovers to get a complete block.
            if Free_Bits_In_Block > 0 then
               Block_Offset := Ctx.Bits_Absorbed / 8;
               Ctx.Block(Block_Offset .. Block_Offset + (Free_Bytes_In_Block - 1))
                 := Data(Data'First .. Data'First + (Free_Bytes_In_Block - 1));

               Offset          := Offset          + Free_Bytes_In_Block;
               Remaining_Bytes := Remaining_Bytes - Free_Bytes_In_Block;
               Remaining_Bits  := Remaining_Bits  - Free_Bits_In_Block;
            end if;

            XOR_Bits_Into_State(Ctx.State,
                                Ctx.Block(0 .. Ctx.Rate - 1),
                                Initial_Bit_Rate);
            F(Ctx.State);

            pragma Assert(Offset + Remaining_Bytes = Initial_Data_Len);
            pragma Assert(Remaining_Bytes = (Remaining_Bits + 7) / 8);

            -- Process complete blocks
            while Remaining_Bits >= Initial_Bit_Rate loop
               pragma Loop_Variant(Decreases => Remaining_Bytes,
                                   Decreases => Remaining_Bits,
                                   Increases => Offset);
               pragma Loop_Invariant(Offset + Remaining_Bytes = Initial_Data_Len
                                     and Remaining_Bytes = (Remaining_Bits + 7) / 8
                                     and (Bit_Length mod 8) = (Remaining_Bits mod 8)
                                     and State_Of(Ctx) = Absorbing
                                     and Rate_Of(Ctx) = Initial_Bit_Rate);

               XOR_Bits_Into_State(Ctx.State,
                                   Data(Data'First + Offset ..
                                       Data'First + (Offset + (Ctx.Rate - 1))),
                                   Initial_Bit_Rate);
               F(Ctx.State);

               Offset          := Offset          + Ctx.Rate;
               Remaining_Bytes := Remaining_Bytes - Ctx.Rate;
               Remaining_Bits  := Remaining_Bits  - Initial_Bit_Rate;
            end loop;

            -- No more complete blocks. Store the leftovers
            if Remaining_Bits > 0 then
               Ctx.Block(0 .. Remaining_Bytes - 1)
                 := Data(Data'First + Offset ..
                           Data'First + (Offset + (Remaining_Bytes - 1)));
            end if;

            -- Prove postcondition
            pragma Assert((Remaining_Bits mod 8) = (Bit_Length mod 8)
                          and State_Of(Ctx) = Absorbing
                          and Remaining_Bits < Rate_Of(Ctx)
                          and Rate_Of(Ctx) = Initial_Bit_Rate);

            Ctx.Bits_Absorbed := Remaining_Bits;

         end if;

      end if;

   end Absorb;


   procedure Absorb_With_Suffix(Ctx        : in out Context;
                                Message    : in     Keccak.Types.Byte_Array;
                                Bit_Length : in     Natural;
                                Suffix     : in     Keccak.Types.Byte;
                                Suffix_Len : in     Natural)
   is
      use type Keccak.Types.Byte;

      Suffix_Array        : Keccak.Types.Byte_Array(0 .. 0) := (0 => Suffix);

      Message_Byte_Length : Natural := (Bit_Length + 7) / 8;
      Message_Last        : Keccak.Types.Index_Number;

      Initial_Rate        : Positive := Rate_Of(Ctx) with Ghost;

   begin
      if Bit_Length = 0 and Suffix_Len > 0 then
         -- In this case the message is empty (length = 0 bits) and there
         -- is at least 1 suffix bit, so we only need to absorb the suffix.
         Absorb(Ctx, Suffix_Array, Suffix_Len);

      elsif Suffix_Len = 0 then
         -- In this case there is no suffix, in which case only the message
         -- needs to be absorbed.
         Absorb(Ctx, Message, Bit_Length);

      elsif Bit_Length mod 8 = 0 then
         -- In this case the message size is a multiple of 8 bits, so we don't
         -- need to worry about packing the suffix bits into message.
         Absorb(Ctx, Message, Bit_Length);

         Suffix_Array(0) := Suffix;
         Absorb(Ctx, Suffix_Array, Suffix_Len);

      else
         -- In this case there is at least 1 suffix bit and the message size is
         -- at least 1 bit. In this case, we need to pack the suffix bits with
         -- the last byte of the message.
         --
         -- There are 2 sub-cases here: either there are enough free bits in the
         -- last byte of the message to hold the entire suffix, or the suffix
         -- is too large to fit in the last byte and must be split across two
         -- bytes.

         Message_Last := Message'First + (((Bit_Length + 7) / 8) - 1);

         pragma Assert(Message_Last in Message'Range);

         if (Bit_Length mod 8) + Suffix_Len <= 8 then
            -- In this case there's enough free bits in the last byte of the
            -- message to store all the suffix bits.

            if Message_Byte_Length > 1 then
               pragma Assert(Message_Last > Message'First);

               -- Process all bytes of the message except the last byte.
               Absorb(Ctx,
                      Message(Message'First .. Message_Last - 1),
                      Bit_Length - (Bit_Length mod 8));
            end if;

            -- Combine last byte of message with the suffix
            Suffix_Array(0) := (Message(Message_Last) and (2**(Bit_Length mod 8) - 1))
              or Shift_Left(Suffix, Bit_Length mod 8);

            pragma Assert((Bit_Length mod 8) + Suffix_Len > 0);

            -- Absorb the last byte of the message + the suffix bits.
            Absorb(Ctx, Suffix_Array, (Bit_Length mod 8) + Suffix_Len);

            -- Prove postcondition
            pragma Assert_And_Cut(State_Of(Ctx) = Absorbing
                                  and (In_Queue_Bit_Length(Ctx) mod 8) = ((Bit_Length + Suffix_Len) mod 8)
                                  and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)
                                  and Rate_Of(Ctx) = Initial_Rate);

         else
            -- In this case the suffix is too large to fit entirely in the
            -- remaining free bits of the message, so we need to split the
            -- suffix across two bytes.

            if Message_Byte_Length > 1 then
               -- Process all bytes of the message except the last byte.
               Absorb(Ctx,
                      Message(Message'First .. Message_Last - 1),
                      (Bit_Length - 8) + (8 - (Bit_Length mod 8)));
            end if;

            -- Append as many suffix bits as possible to the last byte of the
            -- message, then absorb the byte.
            Suffix_Array(0) := (Message(Message'Last) and (2**(Bit_Length mod 8) - 1))
              or Shift_Left(Suffix, Bit_Length mod 8);
            Absorb(Ctx, Suffix_Array, 8);

            pragma Assert_And_Cut(State_Of(Ctx) = Absorbing
                                  and In_Queue_Bit_Length(Ctx) mod 8 = 0
                                  and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)
                                  and Rate_Of(Ctx) = Initial_Rate);

            -- Now absorb the remaining suffix bits.
            Suffix_Array(0) := Interfaces.Shift_Right(Suffix, 8 - (Bit_Length mod 8));
            Absorb(Ctx, Suffix_Array, (Bit_Length + Suffix_Len) mod 8);

            -- Prove Postcondition
            pragma Assert_And_Cut(State_Of(Ctx) = Absorbing
                                  and (In_Queue_Bit_Length(Ctx) mod 8) = ((Bit_Length + Suffix_Len) mod 8)
                                  and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)
                                  and Rate_Of(Ctx) = Initial_Rate);

         end if;
      end if;

      pragma Assert(State_Of(Ctx) = Absorbing
                    and (In_Queue_Bit_Length(Ctx) mod 8) = ((Bit_Length + Suffix_Len) mod 8)
                    and In_Queue_Bit_Length(Ctx) < Rate_Of(Ctx)
                    and Rate_Of(Ctx) = Initial_Rate);
   end Absorb_With_Suffix;



   -- Moves the sponge from the Absorbing state into the Squeezing state.
   --
   -- Any remaining bits in the input queue are absorbed, then the padding
   -- rule is applied and the first bytes are extracted for squeezing.
   procedure Finalize(Ctx : in out Context)
     with Depends => (Ctx => Ctx),
     Post => (State_Of(Ctx) = Squeezing
              and Rate_Of(Ctx) = Rate_Of(Ctx'Old))
   is
      Next_Block : Keccak.Types.Byte_Array(0 .. (State_Size / 8) - 1) := (others => 0);
      Spilled    : Boolean;

   begin

      -- If the input queue is full then absorb the bits before applying the
      -- padding rule.
      if Ctx.Bits_Absorbed >= Rate_Of(Ctx) then
         XOR_Bits_Into_State(Ctx.State,
                             Ctx.Block(0 .. Ctx.Rate - 1),
                             Rate_Of(Ctx));
         F(Ctx.State);

         Ctx.Block := (others => 0);
         Ctx.Bits_Absorbed := 0;
      end if;

      -- Apply the padding rule.
      Pad(Ctx.Block(0 .. Ctx.Rate - 1),
          Ctx.Bits_Absorbed,
          Rate_Of(Ctx),
          Next_Block(0 .. Ctx.Rate - 1),
          Spilled);


      XOR_Bits_Into_State(Ctx.State,
                          Ctx.Block(0 .. Ctx.Rate - 1),
                          Rate_Of(Ctx));
      F(Ctx.State);

      -- Did the padding spill over to another block?
      if Spilled then
         XOR_Bits_Into_State(Ctx.State,
                             Next_Block(0 .. Ctx.Rate - 1),
                             Rate_Of(Ctx));
         F(Ctx.State);
      end if;

      -- Extract the first bytes for squeezing.
      Extract_Data(Ctx.State, Ctx.Block(0 .. Ctx.Rate - 1));

      Ctx.Bits_Absorbed  := 0;
      Ctx.Bytes_Squeezed := 0;
      Ctx.Curr_State     := Squeezing;

   end Finalize;



   procedure Squeeze(Ctx    : in out Context;
                     Digest :    out Keccak.Types.Byte_Array)
   is
      Remaining : Natural := Digest'Length;
      Offset    : Natural := 0;

      Initial_Rate : Positive := Rate_Of(Ctx) with Ghost;
   begin
      Digest := (others => 0); -- workaround for flow analysis

      -- Move from Absorbing state to Squeezing state, if necessary
      if State_Of(Ctx) = Absorbing then
         Finalize(Ctx);
      end if;

      pragma Assert(State_Of(Ctx) = Squeezing);

      -- If there are no leftover bytes then generate a new block.
      if Ctx.Bytes_Squeezed >= Ctx.Rate then
         F(Ctx.State);
         Extract_Data(Ctx.State, Ctx.Block(0 .. Ctx.Rate - 1));
         Ctx.Bytes_Squeezed := 0;
      end if;

      pragma Assert(Offset + Remaining = Digest'Length);

      -- First, squeeze any leftover bytes in the current block
      if Ctx.Bytes_Squeezed > 0 then
         declare
            Bytes_To_Squeeze : Natural := Ctx.Rate - Ctx.Bytes_Squeezed;
         begin
            if Bytes_To_Squeeze > Remaining then
               Bytes_To_Squeeze := Remaining;
            end if;

            Digest(Digest'First + Offset
                   ..
                     Digest'First + ((Offset + Bytes_To_Squeeze)-1))
                := Ctx.Block(Ctx.Bytes_Squeezed ..
                               Ctx.Bytes_Squeezed + (Bytes_To_Squeeze - 1));

            Ctx.Bytes_Squeezed := Ctx.Bytes_Squeezed + Bytes_To_Squeeze;

            Offset    := Offset    + Bytes_To_Squeeze;
            Remaining := Remaining - Bytes_To_Squeeze;
         end;

         -- Permute state if necessary.
         if Ctx.Bytes_Squeezed >= Ctx.Rate then
            F(Ctx.State);
            Extract_Data(Ctx.State, Ctx.Block(0 .. Ctx.Rate - 1));
            Ctx.Bytes_Squeezed := 0;
         end if;
      end if;

      pragma Assert(if Remaining > 0 then Ctx.Bytes_Squeezed = 0);
      pragma Assert(Offset + Remaining = Digest'Length);
      pragma Assert(Rate_Of(Ctx) = Initial_Rate);

      -- Process full blocks
      while Remaining >= Ctx.Rate loop
         pragma Loop_Variant(Increases => Offset,
                             Decreases => Remaining);
         pragma Loop_Invariant((Offset + Remaining = Digest'Length)
                               and State_Of(Ctx) = Squeezing
                               and Rate_Of(Ctx) = Initial_Rate);

         Digest(Digest'First + Offset ..
                  Digest'First + ((Offset + Ctx.Rate) - 1))
             := Ctx.Block(0 .. Ctx.Rate - 1);

         F(Ctx.State);
         Extract_Data(Ctx.State, Ctx.Block(0 .. Ctx.Rate - 1));

         Offset    := Offset    + Ctx.Rate;
         Remaining := Remaining - Ctx.Rate;
      end loop;

      pragma Assert(Remaining < Ctx.Rate);

      -- Process last block
      if Remaining > 0 then
         Digest(Digest'First + Offset ..
                  Digest'First + ((Offset + Remaining) - 1))
             := Ctx.Block(0 .. Remaining - 1);

         Ctx.Bytes_Squeezed := Remaining;
      end if;
   end Squeeze;



end Keccak.Sponge;
