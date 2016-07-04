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
with Interfaces;

package body Keccak.KeccakF
is
   -- Keccak Theta operation
   --
   -- See Algorithm 1 in Section 3.2.1 of NIST FIPS-202
   --
   -- @param A The Keccak input state.
   -- @param AR The Keccak output state after the Theta operation.
   procedure Theta(A  : in     State;
                   AR :    out State)
   is
      C_L : Lane_Type;
      C_R : Lane_Type;
      D   : Lane_Type;
   begin
      for X in X_Coord loop
         C_L := A(X - 1, 0) xor
           A(X - 1, 1) xor
           A(X - 1, 2) xor
           A(X - 1, 3) xor
           A(X - 1, 4);

         C_R := A(X + 1, 0) xor
           A(X + 1, 1) xor
           A(X + 1, 2) xor
           A(X + 1, 3) xor
           A(X + 1, 4);

         D := C_L xor Rotate_Left(C_R, 1);

         AR(X, 0) := A(X, 0) xor D;

         pragma Annotate(GNATprove, False_Positive,
                         """AR"" might not be initialized",
                         "AR is initialized after full loop");

         AR(X, 1) := A(X, 1) xor D;
         AR(X, 2) := A(X, 2) xor D;
         AR(X, 3) := A(X, 3) xor D;
         AR(X, 4) := A(X, 4) xor D;
      end loop;

   end Theta;

   ----------------------------------------------------------------------------
   -- Keccak Rho operation
   --
   -- See Algorithm 2 in Section 3.2.2 of NIST FIPS-202
   --
   -- @param A The Keccak input state.
   -- @param AR The Keccak output state after the Rho operation.
   procedure Rho(A  : in     State;
                 AR :    out State)
   is
   begin
      AR := (0 => (0 => A(0, 0),
                   1 => Rotate_Left(A(0, 1), 36  mod W),
                   2 => Rotate_Left(A(0, 2), 3   mod W),
                   3 => Rotate_Left(A(0, 3), 105 mod W),
                   4 => Rotate_Left(A(0, 4), 210 mod W)
                  ),
             1 => (0 => Rotate_Left(A(1, 0), 1   mod W),
                   1 => Rotate_Left(A(1, 1), 300 mod W),
                   2 => Rotate_Left(A(1, 2), 10  mod W),
                   3 => Rotate_Left(A(1, 3), 45  mod W),
                   4 => Rotate_Left(A(1, 4), 66  mod W)
                  ),
             2 => (0 => Rotate_Left(A(2, 0), 190 mod W),
                   1 => Rotate_Left(A(2, 1), 6   mod W),
                   2 => Rotate_Left(A(2, 2), 171 mod W),
                   3 => Rotate_Left(A(2, 3), 15  mod W),
                   4 => Rotate_Left(A(2, 4), 253 mod W)
                  ),
             3 => (0 => Rotate_Left(A(3, 0), 28  mod W),
                   1 => Rotate_Left(A(3, 1), 55  mod W),
                   2 => Rotate_Left(A(3, 2), 153 mod W),
                   3 => Rotate_Left(A(3, 3), 21  mod W),
                   4 => Rotate_Left(A(3, 4), 120 mod W)
                  ),
             4 => (0 => Rotate_Left(A(4, 0), 91  mod W),
                   1 => Rotate_Left(A(4, 1), 276 mod W),
                   2 => Rotate_Left(A(4, 2), 231 mod W),
                   3 => Rotate_Left(A(4, 3), 136 mod W),
                   4 => Rotate_Left(A(4, 4), 78  mod W)
                  )
            );
   end Rho;

   -- Keccak Pi operation
   --
   -- See Algorithm 3 in Section 3.2.3 of NIST FIPS-202.
   --
   -- @param A The Keccak input state.
   -- @param AR The Keccak output state after the Pi operation.
   procedure Pi(A  : in     State;
                AR :    out State)
   is
   begin
      AR := (0 => (0 => A(0, 0),
                   1 => A(3, 0),
                   2 => A(1, 0),
                   3 => A(4, 0),
                   4 => A(2, 0)
                  ),
             1 => (0 => A(1, 1),
                   1 => A(4, 1),
                   2 => A(2, 1),
                   3 => A(0, 1),
                   4 => A(3, 1)
                  ),
             2 => (0 => A(2, 2),
                   1 => A(0, 2),
                   2 => A(3, 2),
                   3 => A(1, 2),
                   4 => A(4, 2)
                  ),
             3 => (0 => A(3, 3),
                   1 => A(1, 3),
                   2 => A(4, 3),
                   3 => A(2, 3),
                   4 => A(0, 3)
                  ),
             4 => (0 => A(4, 4),
                   1 => A(2, 4),
                   2 => A(0, 4),
                   3 => A(3, 4),
                   4 => A(1, 4)
                  )
            );
   end Pi;

   -- Keccak Chi and Iota operations
   --
   -- See Algorithms 4 and 5 in Sections 3.2.4 and 3.2.5 of NIST FIPS-202.
   --
   -- @param A The Keccak input state
   -- @param AR The Keccak output state after the Chi and Iota operations.
   -- @param RI The current round number/index
   procedure Chi_Iota(A  : in     State;
                      AR :    out State;
                      RI : in     Round_Index)
   is
      use type Interfaces.Unsigned_64;

      type Round_Constants is array(Round_Index) of Interfaces.Unsigned_64;

      RC : constant Round_Constants :=
             (
              16#0000_0000_0000_0001#,
              16#0000_0000_0000_8082#,
              16#8000_0000_0000_808A#,
              16#8000_0000_8000_8000#,
              16#0000_0000_0000_808B#,
              16#0000_0000_8000_0001#,
              16#8000_0000_8000_8081#,
              16#8000_0000_0000_8009#,
              16#0000_0000_0000_008A#,
              16#0000_0000_0000_0088#,
              16#0000_0000_8000_8009#,
              16#0000_0000_8000_000A#,
              16#0000_0000_8000_808B#,
              16#8000_0000_0000_008B#,
              16#8000_0000_0000_8089#,
              16#8000_0000_0000_8003#,
              16#8000_0000_0000_8002#,
              16#8000_0000_0000_0080#,
              16#0000_0000_0000_800A#,
              16#8000_0000_8000_000A#,
              16#8000_0000_8000_8081#,
              16#8000_0000_0000_8080#,
              16#0000_0000_8000_0001#,
              16#8000_0000_8000_8008#
             );
   begin
      -- Process the first set of Y separately to XOR the round constant
      -- with the first lane (this is the Iota part).
      AR(0, 0) := A(0, 0) xor ( (not A(1, 0)) and A(2, 0) ) xor Lane_Type(RC(RI) and (2**W - 1));

      pragma Annotate(GNATprove, False_Positive,
                      """AR"" might not be initialized",
                      "AR is initialized by the end of this procedure");

      AR(1, 0) := A(1, 0) xor ( (not A(2, 0)) and A(3, 0) );
      AR(2, 0) := A(2, 0) xor ( (not A(3, 0)) and A(4, 0) );
      AR(3, 0) := A(3, 0) xor ( (not A(4, 0)) and A(0, 0) );
      AR(4, 0) := A(4, 0) xor ( (not A(0, 0)) and A(1, 0) );

      for Y in Y_Coord range 1 .. Y_Coord'Last loop
         AR(0, Y) := A(0, Y) xor ( (not A(1, Y)) and A(2, Y) );
         AR(1, Y) := A(1, Y) xor ( (not A(2, Y)) and A(3, Y) );
         AR(2, Y) := A(2, Y) xor ( (not A(3, Y)) and A(4, Y) );
         AR(3, Y) := A(3, Y) xor ( (not A(4, Y)) and A(0, Y) );
         AR(4, Y) := A(4, Y) xor ( (not A(0, Y)) and A(1, Y) );
      end loop;
   end Chi_Iota;


   procedure Init(A : out State)
   is
   begin
      A := (others => (others => 0));
   end Init;

end Keccak.KeccakF;
