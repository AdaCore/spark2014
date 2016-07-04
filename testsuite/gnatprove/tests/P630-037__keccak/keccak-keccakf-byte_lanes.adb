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
package body Keccak.KeccakF.Byte_Lanes
is

   procedure XOR_Bits_Into_State(A       : in out State;
                                 Data    : in     Keccak.Types.Byte_Array;
                                 Bit_Len : in     Natural)
   is
      use type Keccak.Types.Byte;

      X                : X_Coord := 0;
      Y                : Y_Coord := 0;

      Remaining_Bits   : Natural := Bit_Len;
      Offset           : Natural := 0;

      Initial_Byte_Len : Natural := (Bit_Len + 7) / 8 with Ghost;

   begin
      -- Process whole lanes (64 bits).
      while Remaining_Bits >= W loop
         pragma Loop_Variant(Increases => Offset,
                             Decreases => Remaining_Bits);
         pragma Loop_Invariant((Offset mod (W/8) = 0)
                               and (Offset + ((Remaining_Bits + 7) / 8) = Initial_Byte_Len));

         declare
            Lane : Lane_Type := 0;
         begin
            for I in Natural range 0 .. (W/8) - 1 loop
               Lane := Lane or Shift_Left(Lane_Type(Data(Data'First + Offset + I)),
                                          I*8);
            end loop;

            A(X, Y) := A(X, Y) xor Lane;
         end;

         X := X + 1;
         if X = 0 then
            Y := Y + 1;
         end if;

         Offset          := Offset          + W/8;
         Remaining_Bits  := Remaining_Bits  - W;
      end loop;

      -- Process any remaining data (smaller than 1 lane - 64 bits)
      if Remaining_Bits > 0 then
         declare
            Word            : Lane_Type := 0;
            Remaining_Bytes : Natural   := (Remaining_Bits + 7) / 8;

         begin
            for I in Natural range 0 .. Remaining_Bytes - 1 loop
               Word := Word or Shift_Left(Lane_Type(Data(Data'First + Offset + I)), I*8);
            end loop;

            A(X, Y) := A(X, Y) xor (Word and (2**Remaining_Bits) - 1);
         end;
      end if;
   end XOR_Bits_Into_State;



   procedure Extract_Bytes(A    : in     State;
                           Data :    out Keccak.Types.Byte_Array)
   is
      use type Keccak.Types.Byte;

      X               : X_Coord := 0;
      Y               : Y_Coord := 0;

      Remaining_Bytes : Natural := Data'Length;
      Offset          : Natural := 0;

      Lane            : Lane_Type;
   begin
      Data := (others => 0); -- workaround for flow analysis.

      -- Case when each lane is at least 1 byte (i.e. 8, 16, 32, or 64 bits)

      -- Process whole lanes
      while Remaining_Bytes >= W/8 loop
         pragma Loop_Variant(Increases => Offset,
                             Decreases => Remaining_Bytes);
         pragma Loop_Invariant(Offset mod (W/8) = 0
                               and Offset + Remaining_Bytes = Data'Length);

         Lane := A(X, Y);

         for I in Natural range 0 .. (W/8) - 1 loop
            Data(Data'First + Offset + I)
              := Keccak.Types.Byte(Shift_Right(Lane, I*8) and 16#FF#);
         end loop;

         X := X + 1;
         if X = 0 then
            Y := Y + 1;
         end if;

         Remaining_Bytes := Remaining_Bytes - W/8;
         Offset          := Offset + W/8;
      end loop;

      -- Process any remaining data (smaller than 1 lane)
      if Remaining_Bytes > 0 then
         Lane := A(X, Y);

         declare
            Shift          : Natural := 0;
            Initial_Offset : Natural := Offset with Ghost;
         begin
            while Remaining_Bytes > 0 loop
               pragma Loop_Variant(Increases => Offset,
                                   Increases => Shift,
                                   Decreases => Remaining_Bytes);
               pragma Loop_Invariant(Offset + Remaining_Bytes = Data'Length
                                     and Shift mod 8 = 0
                                     and Shift = (Offset - Initial_Offset) * 8);

               Data(Data'First + Offset)
                 := Keccak.Types.Byte(Shift_Right(Lane, Shift) and 16#FF#);

               Shift           := Shift + 8;
               Offset          := Offset + 1;
               Remaining_Bytes := Remaining_Bytes - 1;
            end loop;
         end;
      end if;

   end Extract_Bytes;

   procedure Extract_Bits(A       : in     State;
                          Data    :    out Keccak.Types.Byte_Array;
                          Bit_Len : in     Natural)
   is
      use type Keccak.Types.Byte;

   begin
      Extract_Bytes(A, Data);

      -- Avoid exposing more bits than requested by masking away higher bits
      -- in the last byte.
      if Bit_Len > 0 and Bit_Len mod 8 /= 0 then
         Data(Data'Last) := Data(Data'Last) and (2**(Bit_Len mod 8) - 1);
      end if;
   end Extract_Bits;

end Keccak.KeccakF.Byte_Lanes;
