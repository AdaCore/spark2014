-------------------------------------------------------------------------------
-- Copyright (c) 2016 Daniel King
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

package body Keccak.Duplex
is

   procedure Init(Ctx      :    out Context;
                  Capacity : in     Positive)
   is
   begin
      Init_State(Ctx.State);

      Ctx.Rate := State_Size - Capacity;
   end Init;



   procedure Duplex(Ctx                 : in out Context;
                    In_Data             : in     Keccak.Types.Byte_Array;
                    In_Data_Bit_Length  : in     Natural;
                    Out_Data            :    out Keccak.Types.Byte_Array;
                    Out_Data_Bit_Length : in     Natural)
   is
      use type Keccak.Types.Byte;

      Block     : Keccak.Types.Byte_Array(0 .. (State_Size + 7)/8 - 1) := (others => 0);

      Num_Bytes : constant Natural := (In_Data_Bit_Length + 7) / 8;

   begin
      if Num_Bytes > 0 then
         Block(0 .. Num_Bytes - 1)
           := In_Data(In_Data'First .. In_Data'First + (Num_Bytes - 1));
      end if;

      Pad(Block(0 .. ((Rate_Of(Ctx) + 7) / 8) - 1),
          In_Data_Bit_Length,
          Rate_Of(Ctx));

      XOR_Bits_Into_State(Ctx.State,
                          Block(0 .. ((Ctx.Rate + 7) / 8) - 1),
                          Rate_Of(Ctx));

      F(Ctx.State);

      Extract_Bits(Ctx.State, Out_Data, Out_Data_Bit_Length);
   end Duplex;



   procedure Duplex_Blank(Ctx                 : in out Context;
                          Out_Data            :    out Keccak.Types.Byte_Array;
                          Out_Data_Bit_Length : in     Natural)
   is
      use type Keccak.Types.Byte;

      Block   : Keccak.Types.Byte_Array(0 .. (State_Size + 7)/8 - 1) := (others => 0);

   begin
      Pad(Block(0 .. ((Rate_Of(Ctx) + 7) / 8) - 1),
          0,
          Rate_Of(Ctx));

      XOR_Bits_Into_State(Ctx.State,
                          Block(0 .. ((Ctx.Rate + 7) / 8) - 1),
                          Rate_Of(Ctx));

      F(Ctx.State);

      Extract_Bits(Ctx.State, Out_Data, Out_Data_Bit_Length);
   end Duplex_Blank;



   procedure Duplex_Mute(Ctx                : in out Context;
                         In_Data            : in     Keccak.Types.Byte_Array;
                         In_Data_Bit_Length : in     Natural)
   is
      Block   : Keccak.Types.Byte_Array(0 .. (State_Size + 7)/8 - 1) := (others => 0);

   begin
      Block(0 .. In_Data'Length - 1) := In_Data;

      Pad(Block(0 .. ((Rate_Of(Ctx) + 7) / 8) - 1),
          In_Data_Bit_Length,
          Rate_Of(Ctx));

      XOR_Bits_Into_State(Ctx.State,
                          Block(0 .. ((Ctx.Rate + 7) / 8) - 1),
                          Rate_Of(Ctx));

      F(Ctx.State);
   end Duplex_Mute;

end Keccak.Duplex;
