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
   -- The binary logarithm of the lane size.
   --
   -- This determines the Keccak-f state size. Possible values are:
   -- * L=0 => Keccak-f[25]
   -- * L=1 => Keccak-f[50]
   -- * L=2 => Keccak-f[100]
   -- * L=3 => Keccak-f[200]
   -- * L=4 => Keccak-f[400]
   -- * L=5 => Keccak-f[800]
   -- * L=6 => Keccak-f[1600]
   L : in Natural;

   -- Modular type for a lane of the Keccak state.
   --
   -- Lane_Type'Modulus must be equal to 2**(2**L). For example, when L=6
   -- Lane_Type must be a 64-bit mod type (2**L = 64 when L=6).
   type Lane_Type is mod <>;

   -- Bit-wise left shift for Lane_Type.
   with function Shift_Left(Value  : in Lane_Type;
                            Amount : in Natural) return Lane_Type;

   -- Bit-wise right shift for Lane_Type.
   with function Shift_Right(Value  : in Lane_Type;
                             Amount : in Natural) return Lane_Type;

   -- Bit-wise left rotate for Lane_Type.
   with function Rotate_Left(Value  : in Lane_Type;
                             Amount : in Natural) return Lane_Type;

   -- @summary
   -- Generic implementation of the Keccak-f permutations.
   --
   -- @description
   -- This generic package implements the Keccak-f permutations for bit sizes of:
   -- 25, 50, 100, 200, 400, 800, and 1600 bits.
package Keccak.KeccakF
is
   W : constant Positive := 2**L; -- Lane size in bits
   B : constant Positive := W*25; -- State size in bits (1600, 800, etc...)

   type State is private;

   procedure Init(A : out State)
     with Depends => (A => null);
   -- Initialize the Keccak-f state.
   --
   -- Initially, the Keccak state is set to 0.

private
   type X_Coord is mod 5;
   type Y_Coord is mod 5;

   type State is array(X_Coord, Y_Coord) of Lane_Type;

   type Round_Index is new Natural range 0 .. 23;

   procedure Theta(A  : in     State;
                   AR :    out State)
     with Depends => (AR => A),
     Inline;

   procedure Rho(A  : in     State;
                 AR :    out State)
     with Depends => (AR => A),
     Inline;

   procedure Pi(A  : in     State;
                AR :    out State)
     with Depends => (AR => A),
     Inline;

   procedure Chi_Iota(A  : in     State;
                      AR :    out State;
                      RI : in     Round_Index)
     with Depends => (AR => (A, RI)),
     Inline;

end Keccak.KeccakF;
